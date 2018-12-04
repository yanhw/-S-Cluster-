/*	
 *	This programme checks whether a given cluster is a softwired cluster for given phylogenetic network.
 *
 *  =====================!!IMPORTANT!!============================
 *	Before compilation: Change SAT_SOLVER to the address that the SAT solver is installed.
 * 	minisat can be downloaded from http://minisat.se/MiniSat.html
 *  ==============================================================
 *
 *	Compile command: gcc SAT_method.c
 *
 *	Run command:  a.out <network file name> <cluster file name>
 *	Important assumptions:
 *  (1) Maximum size of network is 200.
 *  (2) Each input network represents a valid phylogenetic network in the following format: 
 *			* Nodes are labeled with integers starting from 0 to <number of nodes-1>
 *			* Each line of input represent an edge in the network. For example, "2 5" means there is an edge from noed 2 to node 5
 *  (3) The test cluster is a sbuset of leaves in the input networks.
 *	(The programme "binary_ntk_generator.c" can randomly generates such input networks and culster)
 *
 * 	Oupput is written to file named SAT_<number of leaf>_<number of reticulate node>_<number of network>.txt
 *
 */
#include <stdio.h> 
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Change here to the address of SAT solver.*/
#define SAT_SOLVER "C:\\cygwin\\bin\\minisat"

/* node information */
#define ROOT 0
#define TREE 1
#define RET 2
#define LEAF 3

#define MAXDEGREE 50
#define MAXSIZE  200
#define MAXEDGE  500

struct node {
	int atom;
	int parents[MAXDEGREE];
	int children[MAXDEGREE];
	int type;
	int component_root;
	int in_cluster;
	int reachable_by_node;
	int num_parents;
	int num_children;
};

/* return 0 if (out_copy, node2) is not a edge, 1 otherweise */
int  Check(int node1, int node2, int Edges[][2], int no_edges){
		int i;

		for (i=0; i< no_edges; i++) {
			if (node1==Edges[i][0] && node2==Edges[i][1]) return 1;
		}
		return 0;
}


int update_node_type (int num_parents, int num_children) {
	if (num_parents == 0)
		return ROOT;
	else if (num_children == 0)
		return LEAF;
	else if (num_parents == 1)
		return TREE;
	return RET;
}

int set_tree_component_root (struct node *nodes[], int target) {
	int parent_index;
	parent_index = nodes[target]->parents[0];
	if ((nodes[parent_index]->component_root != -1) && ((nodes[parent_index]->type == TREE)||(nodes[parent_index]->type == ROOT))) {
		return nodes[parent_index]->component_root;
	}
	if (nodes[parent_index]->type != TREE) {
		return target;
	}
	nodes[parent_index]->component_root = set_tree_component_root(nodes, parent_index);
	return nodes[parent_index]->component_root;
}

int set_ret_component_root(struct node *nodes[], int target) {
	int child_index;
	child_index = nodes[target]->children[0];
	if((nodes[child_index]->component_root !=-1)&&(nodes[child_index]->type == RET)) {
		return nodes[child_index]->component_root;
	}
	if (nodes[child_index]->type != RET) {
		return target;
	}
	nodes[child_index]->component_root = set_ret_component_root(nodes, child_index);
	return nodes[child_index]->component_root;
}

void reachable_by_node(struct node *nodes[], int u) {
	int i;
	nodes[u]->reachable_by_node = 1;
	for (i = 0; i < nodes[u]->num_children; i++) {
		reachable_by_node(nodes, nodes[u]->children[i]);
	}
}

void set_component_root_local(struct node *nodes[], int u) {
	int i;
	int child_index;
	for (i = 0; i < nodes[u]->num_children; i++) {
		child_index = nodes[u]->children[i];
		if (nodes[child_index]->type != RET) {
			nodes[child_index]->component_root = nodes[u]->component_root;
			set_component_root_local(nodes, child_index);
		}
	}
}

int is_SAT(int i) {
	FILE *CNF_out;
	char filename[50], result[MAXEDGE];
	
	sprintf(filename, "./0%dCNF.out",i);
	
	CNF_out = fopen(filename, "r");
	fscanf(CNF_out, "%s\n", result);
	fclose(CNF_out);
	if (strcmp(result,"UNSAT") == 0) {
		return 0;
	} else return 1;
}

int find_ret_comp_parents(struct node *nodes[], int ret_index, int counter, int parent_list[]) {
	int parent_index;
	int i;
	int parent_count;
	parent_count = counter;
	for (i = 0; i < nodes[ret_index]->num_parents; i++) {
		parent_index = nodes[ret_index]->parents[i];
		if (nodes[parent_index]->type != RET) {
			parent_list[parent_count] = nodes[parent_index]->component_root;
			parent_count++;
		}
		else {
			parent_count = find_ret_comp_parents(nodes, parent_index, parent_count, parent_list);
		}
	}
	return parent_count;
}

int is_in_cluster(int cluster[], int cluster_size, int leaf_index) {
	int i;
	for (i = 0; i < cluster_size; i++) {
		if (cluster[i] == leaf_index) {
			return 1;
		}
	}
	return 0;
}

int Check_Name(char *node_strings[], int no_nodes, char *str1){
  int i;

  if (str1==NULL) return -1;
  for (i=0; i<no_nodes; i++) {
	if (strcmp(str1, node_strings[i])==0) return i;
  } 
  return -1;
}

int SAT(char *input_filename, char *input_cluster_file) {
	FILE *In;
	FILE *ntk_ptr;
	int i, j, k, root;
	char *node_strings[MAXSIZE];
	char str1[20], str2[20];
	int cluster[MAXSIZE];
	int cluster_size;
	int  start[MAXEDGE], end[MAXEDGE];
	int no_edges, no_nodes;
	struct node *nodes[MAXSIZE];
	int tree_node_list[MAXSIZE];
	int ret_node_list[MAXSIZE];
	int leaf_node_list[MAXSIZE];
	int num_tree_node, num_ret_node, num_leaf_node;
	int modified = 0;
	int target;
	int original_parent;
	int atom_count;
	int CNF[MAXSIZE][MAXSIZE], sign[MAXSIZE][MAXSIZE];
	int clause_size[MAXSIZE];
	int num_clause;
	char CNF_filename[100];
	FILE *CNF_file;
	char command[100];
	int leaf_root;
	int UNSAT_flag;
	int ret_root;
	int ret_comp_parents[MAXSIZE];
	int num_parents;
	int in_ret_clause[MAXSIZE];
	int parent_index, new_comp_count, literal_count;
	int child_index;
	int leaf_index;
	int node_check[MAXSIZE][MAXSIZE];
	int UNSAT_node[MAXSIZE];


	/* read clustering */
	cluster_size = 0;
   	In=fopen(input_cluster_file, "r");
   	if (In ==NULL) printf("Cluster_file_name is not readable\n");
   	while (fscanf(In, "%s\n", str1)!=EOF){
      	cluster[cluster_size] = atoi(str1);
      	cluster_size++;
   	}
   	fclose(In);

   	/*Cluster only contains one node, trivial problem*/
   	if (cluster_size == 1){
   		return 1;
   	}

   	/*Read network from file*/
   	ntk_ptr=fopen(input_filename, "r");
   	no_edges=0;  no_nodes=0;
   	while (fscanf(ntk_ptr, "%s %s\n", str1, str2)!=EOF){
	    k=Check_Name(node_strings, no_nodes, str1);
    	if (k==-1) {
     		k=no_nodes,  no_nodes=1+no_nodes;
	    	node_strings[k]=(char *)malloc(strlen(str1)+1);
	    	strcpy(node_strings[k], str1);
	    }
		start[no_edges]=k;
	    k=Check_Name(node_strings, no_nodes, str2);
	    if (k==-1) {
	     	k=no_nodes,  no_nodes=1+no_nodes;
		    node_strings[k]=(char *)malloc(strlen(str2)+1);
		    strcpy(node_strings[k], str2);
	    }
        end[no_edges]=k; no_edges +=1;
   	}
   	fclose(ntk_ptr);

   	/*Build network*/
   	for (i = 0; i < no_nodes; i++){
   		nodes[i] = (struct node*)malloc(sizeof(struct node));
   		nodes[i]->num_children = 0;
   		nodes[i]->num_parents = 0;
   		nodes[i]->component_root = -1;
   	}
   
   	/*add edge*/
   	for (i = 0; i < no_edges; i++) {
   		nodes[start[i]]->children[nodes[start[i]]->num_children] = end[i];
   		nodes[start[i]]->num_children +=1;
   		nodes[end[i]]->parents[nodes[end[i]]->num_parents] = start[i];
   		nodes[end[i]]->num_parents +=1;
   	}
   	

   	/*update node type and update list by node types*/
   	num_tree_node = 0;
   	num_ret_node = 0;
   	num_leaf_node = 0;
   	for (i = 0; i < no_nodes; i++) {
   		nodes[i]->type = update_node_type(nodes[i]->num_parents,nodes[i]->num_children);
   		if (nodes[i]->type == ROOT)
   			root = i;
   		if (nodes[i]->type == TREE) {
   			tree_node_list[num_tree_node] = i;
   			num_tree_node++;
   		}
   		else if (nodes[i]->type == RET) {
   			ret_node_list[num_ret_node] = i;
   			num_ret_node++;
   		}
   		if (nodes[i]->type ==LEAF) {
   			leaf_node_list[num_leaf_node] = i;
   			num_leaf_node++;
   		}
   	}

   	/*All leafs are inside cluster, trivial oroblem*/
   	if (num_leaf_node == cluster_size) {
   		for (i = 0; i < no_nodes; i++) {
   			free(nodes[i]);
   		}
   		return 1;
   	}

   	/*update component root*/
   	nodes[root]->component_root = root;
   	for (i = 0; i < no_nodes; i++) {
   		if (nodes[i]->component_root == -1) {
   			if ((nodes[i]->type == TREE)||(nodes[i]->type == LEAF)) {
   				nodes[i]->component_root = set_tree_component_root(nodes,i);
   			}
   			else if (nodes[i]->type == RET) {
   				nodes[i]->component_root = set_ret_component_root(nodes,i);
   			}
   		}
   	}

   	/*print network (for debugging)
   	for (i = 0; i < no_nodes; i++) {
   		printf("id = %d; type = %d; component_root = %d\n", i, nodes[i]->type, nodes[i]->component_root);
   	}*/

   	/*detect trivially UNSAT nodes*/
   	for (i = 0; i < no_nodes; i++) {
   		UNSAT_node[i] = 0;
   	}
   	for (i = 0; i < num_leaf_node; i++) {
   		for (j = 0; j < no_nodes; j++) {
   			node_check[i][j] = 0;
   		}
   	}
   	for (i = 0; i < num_leaf_node; i++)	{
   		leaf_index = leaf_node_list[i];
   		node_check[i][leaf_index] = 1;
   		for (j = no_nodes-num_leaf_node-1; j >= 0; j--) {
   			for (k = 0; k < nodes[j]->num_children; k++) {
   				node_check[i][j] += node_check[i][nodes[j]->children[k]];
   			}
   		}
   	}

   	
   	for (j = 0; j < no_nodes - num_leaf_node; j++) {
   		for (i = 0; i < num_leaf_node; i++) {
   			leaf_index = leaf_node_list[i];
   			if (is_in_cluster(cluster, cluster_size, leaf_index) == 1) {
   				if (node_check[i][j] == 0) {
   					UNSAT_node[j] = 1;
   				}
   			}

   			if (UNSAT_node[j] == 1) {
   				continue;
   			}
   		}
   	}

   	/*SCCP for all tree nodes*/
   	for (i = 0; i < num_tree_node; i++){
   		target = tree_node_list[i];
   		UNSAT_flag = 0;

   		/*skip trivial cases*/
   		if (UNSAT_node[target] == 1) {
   			continue;
   		}

   		/* add additional node if necessary*/
   		modified = 0;
   		if (target != nodes[target]->component_root) {
   			original_parent = nodes[target]->parents[0];

   			nodes[target]->component_root = target;
   			set_component_root_local(nodes, target);
   			modified = 1;
   		}

   		/* reachable by target node u*/
   		for (j = 0; j < no_nodes; j++) {
   			nodes[j]->reachable_by_node = 0;
   		}
   		reachable_by_node(nodes, target);

   		/*terminate the case if a leaf in cluster is not reachable*/
   		for (j = 0; j < cluster_size; j++) {
   			if (nodes[cluster[j]]->reachable_by_node == 0)
   				UNSAT_flag = 1;
   		}

   		if (UNSAT_flag == 1) {
   	/*		printf("UNSAT because cluster not reachable from u!\n");*/
   			/* reset the network if modified for SCCP instance*/
   			if (modified == 1) {
   				nodes[target]->component_root = nodes[original_parent]->component_root;
   				set_component_root_local(nodes, target);
   			}
   			continue;
   		}

   		/*build CNF*/   		
   		for (j = 0; j < no_nodes; j++) {
   			nodes[j]->atom = -1;
   			nodes[j]->in_cluster = 0;
   		}
   		for (j = 0; j < MAXSIZE; j++) {
   			clause_size[j] = 0;
   		}
		
		/*root clause*/
   		atom_count = 1;
   		num_clause = 1;
   		clause_size[0] = 1;
   		nodes[target]->atom = 1;
   		nodes[target]->in_cluster = 2;
   		CNF[0][0] = 1;
   		sign[0][0] = 1;

   		/*leaf clause*/
   		for (j = 0; j < cluster_size; j++) {
   			leaf_root = nodes[cluster[j]]->component_root;
   			nodes[leaf_root]->in_cluster = 2;
   			nodes[cluster[j]]->in_cluster = 1;
   			if (nodes[leaf_root]->atom == -1) {
   				atom_count++;
   				nodes[leaf_root]->atom = atom_count;
   				CNF[num_clause][0] = nodes[leaf_root]->atom;
   				sign[num_clause][0] = 1;
   				clause_size[num_clause] = 1;
   				num_clause++;
   			}
   		}

   		for (j = 0; j < num_leaf_node; j++) {
   			if (nodes[leaf_node_list[j]]->in_cluster == 1) {
   				continue;
   			}
   			leaf_root = nodes[leaf_node_list[j]]->component_root;
   			if (nodes[leaf_root]->in_cluster == 2) {
   				UNSAT_flag = 1;
   				break;
   			}
   			else if (nodes[leaf_root]->atom == -1) {
   				atom_count++;
   				nodes[leaf_root]->atom = atom_count;
   				CNF[num_clause][0] = nodes[leaf_root]->atom;
   				sign[num_clause][0] = -1;
   				clause_size[num_clause] = 1;
   				num_clause++;
   			} 
   		}
   		if (UNSAT_flag == 1) {
   /*			printf("UNSAT because leaf conflict!\n");		*/
   			/* reset the network if modified for SCCP instance*/
   			if (modified == 1) {
   				nodes[target]->component_root = nodes[original_parent]->component_root;
   				set_component_root_local(nodes, target);
   			}
   			continue;
   		}

   		/*reticulate clause*/
   		for (j = 0; j < num_ret_node; j++) {
   			ret_root = nodes[ret_node_list[j]]->component_root;
   			/*skip if not reachable*/
   			if (nodes[ret_root]->reachable_by_node == 0) {
   				continue;
   			}

   			if (nodes[ret_root]->atom != -2) {  				
   				for (k = 0; k < no_nodes; k++) {
   					in_ret_clause[k] = 0;
   				}

   				child_index = nodes[ret_root]->children[0];
   				if (nodes[child_index]->atom == -1) {
   					atom_count++;
   					nodes[child_index]->atom = atom_count;
   				}

   				CNF[num_clause][0] =  nodes[child_index]->atom;
   				CNF[num_clause+1][0] = nodes[child_index]->atom;
   				sign[num_clause][0] = 1;
   				sign[num_clause+1][0] = -1;

   				new_comp_count = 0;
   				literal_count = 1;
   				num_parents = find_ret_comp_parents(nodes, ret_root, 0, ret_comp_parents);
   				for (k = 0; k < num_parents; k++) {
   					parent_index = ret_comp_parents[k];
   					if (in_ret_clause[parent_index] == 1) {
   						continue;
   					}
   					/*assign atom label if the component is new*/
   					if (nodes[parent_index]->atom == -1) {
   						atom_count++;
   						nodes[parent_index]->atom = atom_count;
   						/*add singleton clause if component is not reachable*/
   						if (nodes[parent_index]->reachable_by_node != 1) {
   							CNF[num_clause+2+new_comp_count][0] = nodes[parent_index]->atom;
   							sign[num_clause+2+new_comp_count][0] = -1;
   							clause_size[num_clause+2+new_comp_count] = 1;
   							new_comp_count++;
   						}
   					}

   					CNF[num_clause][literal_count] = nodes[parent_index]->atom;
   					CNF[num_clause+1][literal_count] = nodes[parent_index]->atom;
   					sign[num_clause][literal_count] = -1;
   					sign[num_clause+1][literal_count] = 1;
   					literal_count++;

   					in_ret_clause[parent_index] = 1;
   				}
   				clause_size[num_clause] = literal_count;
   				clause_size[num_clause+1] = literal_count;
   				num_clause += 2+new_comp_count;
   				nodes[ret_root]->atom = -2;
   			}
   		}

   		/*write CNF to file*/
   		sprintf(CNF_filename, "./0%dCNF.in",i);
   		CNF_file=fopen(CNF_filename, "w");
       	if (CNF_file!=NULL){
       		fprintf(CNF_file, "p cnf %d %d\n",atom_count,num_clause);
       		for (j = 0; j < num_clause; j++) {
       			for (k = 0; k < clause_size[j]; k++) {
       				if (sign[j][k] == -1) {
       					fprintf(CNF_file, "-");
       				}
       				fprintf(CNF_file, "%d ", CNF[j][k]);
       			}
       			fprintf(CNF_file, "0\n");
       		}
       	}
       	fclose(CNF_file);

       	/*call minisat and return 1 if satsfiable*/
       	sprintf(command, "%s 0%dCNF.in 0%dCNF.out",SAT_SOLVER, i,i);
       	system(command);
       	if (is_SAT(i) == 1) {
   			for (i = 0; i < no_nodes; i++) {
   				free(nodes[i]);
   			}
       		return 1;
       	}

   		/* reset the network if modified for SCCP instance*/
   		if (modified == 1) {
   			nodes[target]->component_root = nodes[original_parent]->component_root;
   			set_component_root_local(nodes, target);
   		}
   	}

   	/*Negative result for all nodes, return 0*/
   	for (i = 0; i < no_nodes; i++) {
   		free(nodes[i]);
   	}
	return 0;
}



int main(int argc, char *argv[]){
	int result;

	result = SAT(argv[1], argv[2]);	

	if(result == 1) {
			printf("The subset is a cluster of input network.\n");
	}
	else {
			printf("The subset is not a cluster of input network.\n");
	}


	return 0;
}

