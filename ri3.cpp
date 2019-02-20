/*
Copyright (c) 2014 by Rosalba Giugno

This library contains portions of other open source products covered by separate
licenses. Please see the corresponding source files for specific terms.

RI is provided under the terms of The MIT License (MIT):

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

#include <iostream>
#include <fstream>
#include <string>
#include <cstdlib>
#include <ctime>


#include <stdio.h>
#include <stdlib.h>
#include "c_textdb_driver.h"
#include "timer.h"


#include "AttributeComparator.h"
#include "AttributeDeconstructor.h"
#include "Graph.h"
#include "MatchingMachine.h"
#include "MaMaConstrFirst.h"
#include "Match.h"

//#define FIRST_MATCH_ONLY  //if setted, the searching process stops at the first found match
#include "Solver.h"
#include "IsoGISolver.h"
#include "SubGISolver.h"
#include "InducedSubGISolver.h"

//#define PRINT_MATCHES
//#define CSV_FORMAT

#include <map>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/vf2_sub_graph_iso.hpp>

struct comp_label { 
    std::string label;
 };
using graph_type = boost::adjacency_list<boost::vecS, boost::vecS, boost::undirectedS, comp_label, comp_label>;


using namespace rilib;

void rigraph_to_boost(Graph& ri, graph_type& bst) {
    std::map<int, graph_type::vertex_descriptor> vertices;
    for (int i = 0; i < ri.nof_nodes; ++i) { 
        vertices.emplace(i, boost::add_vertex(bst));
        bst[vertices[i]].label = *(std::string*)ri.nodes_attrs[i];
    }
    for (int i = 0; i < ri.nof_nodes; ++i) {
        for (int j = 0; j < ri.out_adj_sizes[i]; ++j) {
            int k = ri.out_adj_list[i][j];
            if (k > i) {
                graph_type::edge_descriptor edge = boost::add_edge(vertices[i], vertices[k], bst).first;
                bst[edge].label = *(std::string*)ri.out_adj_attrs[i][j];
            }
        }
    }
}


void usage(char* args0);
int match(MATCH_TYPE matchtype, GRAPH_FILE_TYPE filetype,	std::string& referencefile,	std::string& queryfile);

int main(int argc, char* argv[]){

	if(argc!=5){
		usage(argv[0]);
		return -1;
	}

	MATCH_TYPE matchtype;
	GRAPH_FILE_TYPE filetype;
	std::string reference;
	std::string query;

	std::string par = argv[1];
	if(par=="iso"){
		matchtype = MT_ISO;
	}
	else if(par=="ind"){
		matchtype = MT_INDSUB;
	}
	else if(par=="mono"){
		matchtype = MT_MONO;
	}
	else{
		usage(argv[0]);
		return -1;
	}

	par = argv[2];
	if(par=="gfu"){
		filetype = GFT_GFU;
	}
	else if(par=="gfd"){
		filetype = GFT_GFD;
	}
	else if(par=="gfda"){
			filetype = GFT_GFDA;
		}
	else if(par=="geu"){
		filetype = GFT_EGFU;
	}
	else if(par=="ged"){
		filetype = GFT_EGFD;
	}
	else if(par=="vfu"){
		filetype = GFT_VFU;
	}
	else{
		usage(argv[0]);
		return -1;
	}

	reference = argv[3];
	query = argv[4];

	return match(matchtype, filetype, reference, query);
};





void usage(char* args0){
	std::cout<<"usage "<<args0<<" [iso ind mono] [gfu gfd gfda geu ged vfu] reference query\n";
	std::cout<<"\tmatch type:\n";
	std::cout<<"\t\tiso = isomorphism\n";
	std::cout<<"\t\tind = induced subisomorphism\n";
	std::cout<<"\t\tmono = monomorphism\n";
	std::cout<<"\tgraph input format:\n";
	std::cout<<"\t\tgfu = undirect graphs with labels on nodes\n";
	std::cout<<"\t\tgfd = direct graphs with labels on nodes\n";
	std::cout<<"\t\tgfd = direct graphs with one single label on nodes\n";
	std::cout<<"\t\tgeu = undirect graphs with labels both on nodes and edges\n";
	std::cout<<"\t\tged = direct graphs with labels both on nodes and edges\n";
	std::cout<<"\t\tvfu = VF2Lib undirect unlabeled format\n";
	std::cout<<"\treference file contains one or more reference graphs\n";
	std::cout<<"\tquery contains the query graph (just one)\n";
};

struct boost_callback {
    static long match_count;
    graph_type* graph_small;
    graph_type* graph_large;
    boost_callback(graph_type* gs, graph_type* gl) : graph_small(gs), graph_large(gl) { }
    template <class CMap1to2, class CMap2to1>
    bool operator()(CMap1to2, CMap2to1) { ++match_count; return true; }
    bool operator()(graph_type::vertex_descriptor vs, graph_type::vertex_descriptor vl) {
        return (*graph_small)[vs].label == (*graph_large)[vl].label;
    }
    bool operator()(graph_type::edge_descriptor vs, graph_type::edge_descriptor vl) {
        return (*graph_small)[vs].label == (*graph_large)[vl].label;
    }
};

long boost_callback::match_count = 0;

int match(
		MATCH_TYPE 			matchtype,
		GRAPH_FILE_TYPE 	filetype,
		std::string& 		referencefile,
		std::string& 	queryfile){

	TIMEHANDLE load_s, load_s_q, make_mama_s, match_s, total_s, boost_s;
	double load_t=0;double load_t_q=0; double make_mama_t=0; double match_t=0; double total_t=0; double boost_load_t=0; double boost_match_t=0; double boost_prep_t=0;
	total_s=start_time();

	bool takeNodeLabels = false;
	bool takeEdgesLabels = false;
	int rret;

	AttributeComparator* nodeComparator;			//to compare node labels
	AttributeComparator* edgeComparator;			//to compare edge labels
	switch(filetype){
		case GFT_GFU:
		case GFT_GFD:
			// only nodes have labels and they are strings
			nodeComparator = new StringAttrComparator();
			edgeComparator = new DefaultAttrComparator();
			takeNodeLabels = true;
			break;
		case GFT_GFDA:
			nodeComparator = new DefaultAttrComparator();
			edgeComparator = new DefaultAttrComparator();
			takeNodeLabels = true;
			break;
		case GFT_EGFU:
		case GFT_EGFD:
			//labels on nodes and edges, both of them are strings
			nodeComparator = new StringAttrComparator();
			edgeComparator = new StringAttrComparator();
			takeNodeLabels = true;
			takeEdgesLabels = true;
			break;
		case GFT_VFU:
			//no labels
			nodeComparator = new DefaultAttrComparator();
			edgeComparator = new DefaultAttrComparator();
			break;
    default:
      return -1;
	}

	TIMEHANDLE tt_start;
	double tt_end;



	//read the query graph
	load_s_q=start_time();
	Graph *query = new Graph();
	rret = read_graph(queryfile.c_str(), query, filetype);
	load_t_q+=end_time(load_s_q);
	if(rret !=0){
		std::cout<<"error on reading query graph\n";
	}
    boost_s=start_time();
    graph_type *query_boost = new graph_type();
    rigraph_to_boost(*query, *query_boost);
    boost_load_t+=end_time(boost_s);
	long 	steps = 0,				//total number of steps of the backtracking phase
			triedcouples = 0, 		//nof tried pair (query node, reference node)
			matchcount = 0, 		//nof found matches
            boostmatchcount = 0,
			matchedcouples = 0;		//nof mathed pair (during partial solutions)
	long tsteps = 0, ttriedcouples = 0, tmatchedcouples = 0;

	FILE *fd = open_file(referencefile.c_str(), filetype);
	if(fd != NULL){
#ifdef PRINT_MATCHES
		//to print found matches on screen
		MatchListener* matchListener=new EmptyMatchListener();// ConsoleMatchListener();
#else
		//do not print matches, just count them
		MatchListener* matchListener=new EmptyMatchListener();
#endif
		int i=0;
		bool rreaded = true;
		do{//for each reference graph inside the input file
#ifdef PRINT_MATCHES
			std::cout<<"#"<<i<<"\n";
#endif
			//read the next reference graph
			load_s=start_time();
			Graph * rrg = new Graph();
			int rret = read_dbgraph(referencefile.c_str(), fd, rrg, filetype);
			rreaded = (rret == 0);
			load_t+=end_time(load_s);
			if(rreaded){
                    boost_s=start_time();
                    graph_type *rrg_boost = new graph_type();
                    rigraph_to_boost(*rrg, *rrg_boost);
                    boost_load_t+=end_time(boost_s);

	                make_mama_s=start_time();
	                MaMaConstrFirst* mama = new MaMaConstrFirst(*rrg);
	                mama->build(*rrg);
	                make_mama_t+=end_time(make_mama_s);

					//run the matching
					match_s=start_time();
					match(	*query,
							*rrg,
							*mama,
							*matchListener,
							matchtype,
							*nodeComparator,
							*edgeComparator,
							&tsteps,
							&ttriedcouples,
							&tmatchedcouples);
					match_t+=end_time(match_s);

                    //run the boost matching
                    boost_s=start_time();
                    boost_callback cb(rrg_boost, query_boost);
                    boost_prep_t+=end_time(boost_s);

                    boost_s=start_time();
                    boost::vf2_subgraph_iso(*rrg_boost, *query_boost, cb, boost::get(boost::vertex_index, *rrg_boost), boost::get(boost::vertex_index, *query_boost), boost::vertex_order_by_mult(*rrg_boost), cb, cb);
                    boost_match_t+=end_time(boost_s);

					//see rilib/Solver.h
//					steps += tsteps;
//					triedcouples += ttriedcouples;
					matchedcouples += tmatchedcouples;
                    delete rrg_boost;
                    delete mama;
				}
        delete rrg;
				
			i++;
		}while(rreaded);

		matchcount = matchListener->matchcount;

		delete matchListener;

		fclose(fd);
	}
	else{
		std::cout<<"unable to open reference file\n";
		return -1;
	}

	total_t=end_time(total_s);

#ifdef CSV_FORMAT
	std::cout<<referencefile<<"\t"<<queryfile<<"\t";
	std:cout<<load_t_q<<"\t"<<make_mama_t<<"\t"<<load_t<<"\t"<<match_t<<"\t"<<total_t<<"\t"<<steps<<"\t"<<triedcouples<<"\t"<<matchedcouples<<"\t"<<matchcount;
#else
	/*std::cout<<"reference file: "<<referencefile<<"\n";
	std::cout<<"query file: "<<queryfile<<"\n";
	std::cout<<"total time: "<<total_t<<"\n";
	std::cout<<"matching time: "<<match_t<<"\n";
    std::cout<<"boost matching time: "<<boost_match_t<<"\n";
	std::cout<<"number of found matches: "<<matchcount<<"\n";
    std::cout<<"boost found matches: "<<boost_callback::match_count<<"\n";
	std::cout<<"search space size: "<<matchedcouples<<"\n";
    std::cout<<"make mama time: "<<make_mama_t<<"\n";
    std::cout<<"load time: "<<load_t_q + load_t<<"\n";
    std::cout<<"boost load time: "<<boost_load_t<<"\n";
    */
    std::cout<<boost_match_t/match_t<<"\n";
#endif

  delete mama;
  delete query;
  
  delete nodeComparator;
  delete edgeComparator;
  
	return 0;
};





