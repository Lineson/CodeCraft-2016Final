#include "route.h"
#include "lib_record.h"
#include <stdio.h>


#include <string.h>    /* memcpy */
#include <math.h>      /* exp    */
#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>

#include <time.h>
#include <sys/timeb.h>
#include <sys/time.h>

#define DEBUG 1
#ifdef DEBUG
    #define DBG printf
#else
    #define DBG(format, arg...) do { ; } while (0)
#endif



struct timeval begin_time;
struct timeval end_time;
double duration;
//---------------------------global struct and data below-----------------------------//

/*AS parameters*/
double AS_T_INIT              = 100;
double AS_FINAL_T             = 0.1;
double AS_COOLING             = 0.99; /* to lower down T (< 1) */
long long   AS_seed           = -314159L;

int    AS_no_change_time      = 200;
int    AS_TRIES_PER_T         = 400;
int    AS_IMPROVED_PATH_PER_T = 5;


int    AS_no_change_time_for_init  = 20;
int    AS_TRIES_PER_T_for_init     = 100;
int    AS_max_cut_num = 0;



/** global graph info **/
int  INF       = 100000000;  // ZP 3-22
int  INF_REUSE = 200000;



int data[2008][2008]; // raw topo marked by edge id
int data2[2008][2008];
int w[40000]; // weight of each edge
int g[2008][2008]; // graph topo to work on --Directed Distance
int g2[2008][2008];
int adj[2008][200]; // adjacency list -- adj[i][0] : number of neighbors

int max_v; // number of vertexes = n
int max_e; // number of edges
int s; // vertex s
int t; // vertex t

/** global info of graph-1 **/
int max_vs1; // numbers of specified vertexes
int spec1[108];
bool isVspec1[2008]; /* mark the specific node vetex */

/** global info of graph-2 **/
int max_vs2; // numbers of specified vertexes
int spec2[108];
bool isVspec2[2008];

/*final path writes to file*/
int path1[2004];
int path2[2004];


short int edgesCount[40004];

typedef struct reused_VSnode
{
    int vsID;
    struct reused_VSnode *next;
}ReusdVS;


typedef struct tspstruct {

    long long int bestlen;             /* record best object */
    int *border2; 
    int *border1;            /* record best order ever found */

    int *cnt_arc;            /* arc used info, 0 <= cnt_arc[0-20000] <= 2 */
    int reused_num;          /* 0 <= reused_num <= 40000 */
    int tmp_reused_num;//del?


    /** inter-med info of graph-1 **/
    long long int best_len1;
    int *iorder1;
    int *iorder_pre1;//?
    bool *isVisted1;          /* if visited between s and t */
    // int reused_VsID_num1;     /*reused Vs1 node numbers*/
    // struct reused_VSnode* reused_head1;


    /** inter-med info of graph-2 **/
    long long int best_len2;
    int *iorder2;
    int *iorder_pre2;//?
    bool *isVisted2;
    // int reused_VsID_num2;    /*reused Vs2 node numbers*/
    // struct reused_VSnode* reused_head2;

} TSP;

/*global var to record cut infos below*/
typedef struct cutPlace
{
    int head;
    int tail;
}CutP;
#define MAX_CUT_NUM 101
/*global var to record cut infos above*/

//---------------------------global struct and data above-----------------------------//



/*random functions*/
#define PRANDMAX 1000000000
static int aNum = 0;
static int bNum = 0;
static int arr[55];
int Rand();
void initRand (int seed)
{
    int i, ii;
    int last, next;

    seed %= PRANDMAX;
    if (seed < 0) seed += PRANDMAX;

    arr[0] = last = seed;
    next = 1;
    for (i = 1; i < 55; i++) {
        ii = (21 * i) % 55;
        arr[ii] = next;
        next = last - next;
        if (next < 0)
            next += PRANDMAX;
        last = arr[ii];
    }
    aNum = 0;
    bNum = 24;
    for (i = 0; i < 165; i++)
        last = Rand ();
}

int Rand (void)
{
    int tp;

    if (aNum-- == 0)
        aNum = 54;
    if (bNum-- == 0)
        bNum = 54;
    if (aNum > 54 || bNum > 54)
    {
        aNum = aNum%55;
        bNum = bNum%55;
    }
    tp = arr[aNum] - arr[bNum];

    if (tp < 0)
        tp += PRANDMAX;

    arr[aNum] = tp;

    return tp;
}
// #define unifRand(n) (Rand()%n)
int unifRand(int n){
    if (n <= 1)
        return 0;
    else
        return Rand()%n;
}

#define PARA_MAX 100000000
/*Accept probability of replacing node in [s,t] with [t+1,n]*/
#define PARA_01 ((double)Rand()/PARA_MAX)  
/*Accept probability of exchange between [s,t]*/
#define PARA_02 ((double)Rand()/PARA_MAX)






//-------------------------------------------find path--------------------------------------//
#define max_cost INF
#define V_SIZE 2004
int dfs_cnt = 0;

int src; // current source
int dst; // current destination

         // Dijkstra data type
bool visited[V_SIZE]; // visit hash table
int dist[V_SIZE]; // shortest path distance
int dist_heap[V_SIZE]; // shortest path heap -- start from heap[1]
int heap_size; // current heap size
int loc[V_SIZE]; // location of each vertex in heap

int best; // current best cost
bool path_vis[V_SIZE];
int next[V_SIZE];


struct cutPlace cut[200];
int get_tail[V_SIZE];
int max_cut;

/*----find path lib----*/
int get_src(int *u, int *v) {
    int idx = Rand() % max_cut;
    *v = cut[idx].tail;
    *u = get_tail[*v];
    return idx;
}

void up(int x, int heap[], int *size) {
    int i = loc[x];
    while (i > 1 && dist[heap[i]] < dist[heap[i / 2]]) {
        heap[i] = heap[i] ^ heap[i / 2];
        heap[i / 2] = heap[i] ^ heap[i / 2];
        heap[i] = heap[i] ^ heap[i / 2];
        loc[heap[i]] = i;
        loc[heap[i / 2]] = i / 2;
        i = i / 2;
    }
}

void down(int x, int heap[], int *size) {
    int i = loc[x];
    int k;
    while ((i + i <= (*size) && dist[heap[i]] > dist[heap[i + i]]) ||
        (i + i + 1 <= (*size) && dist[heap[i]] > dist[heap[i + i + 1]])) {
        k = i + i;
        if (k + 1 <= (*size) && dist[heap[k]] > dist[heap[k + 1]]) {
            k++;
        }
        heap[i] = heap[i] ^ heap[k];
        heap[k] = heap[i] ^ heap[k];
        heap[i] = heap[i] ^ heap[k];
        loc[heap[i]] = i;
        loc[heap[k]] = k;
        i = k;
    }
}

void push(int x, int heap[], int *size) {
    (*size)++;
    heap[*size] = x;
    loc[x] = *size;
    up(x, heap, size);
}

int pop(int heap[], int *size) {
    int ans = heap[1];
    heap[1] = heap[*size];
    heap[*size] = -1;
    loc[heap[1]] = 1;
    (*size)--;
    down(heap[1], heap, size);
    return ans;
}
/*----find path lib----*/

int queue[2 * V_SIZE];
int head;
int tail;


int cur;
int max_dep;
long long int cur_cost;
int MAX_DFS = 0;

//--------------find 1 ----------------//
void find_path_bfs(int begin, int pre[]) {
    //memset(dist, 0, sizeof(dist));
    //memset(queue, 0, sizeof(queue));
    //memset(visited, 0, sizeof(visited));
    //memset(pre, 0xff, sizeof(dist));
    for (int i = 0; i < max_v; i++) {
        dist[i] = 0;
        queue[i + i] = -1;
        queue[i + i + 1] = -1;
        visited[i] = 0;
        pre[i] = -1;
    }
    head = 0;
    tail = 0;
    int u, v;
    int len = adj[begin][0];
    for (int i = 1; i <= len; i++) {
        v = adj[begin][i];
        if (!path_vis[v]) {
            queue[tail] = v;
            pre[v] = begin;
            dist[v] = 1;
            visited[v] = true;
            tail = (tail + 1) % (2 * max_v);
        }
    }
    while (head != tail) {
        u = queue[head];
        head = (head + 1) % (2 * max_v);
        if (u == dst)
            continue;
        u = get_tail[u];
        len = adj[u][0];
        for (int i = 1; i <= len; i++) {
            v = adj[u][i];
            if (!visited[v] && !path_vis[v]) {
                if (pre[u] >= 0 && !isVspec1[u])    //22222222222222
                    pre[v] = u;
                visited[v] = true;
                queue[tail] = v;
                dist[v] = dist[u] + 1;
                tail = (tail + 1) % (2 * max_v);
            }
        }
    }
}

int best_path1[V_SIZE];
bool best_vis1[V_SIZE];

void get_result() {
    memcpy(&best_path1[0], &next[0], max_v * sizeof(int));
    memcpy(&best_vis1[0], &path_vis[0], max_v * sizeof(bool));
}

void dfs(int u, int dep, int cost) {
    if (dep > max_dep || (u == src && dep == max_cut && cost < best)) {
        cur = u;
        cur_cost = cost;
        max_dep = dep;
        get_result();
        if (u == src && dep == max_cut) {
            best = cost;
            cur_cost = best;
            //printf("%d\n", best);
            return;
        }
    }
    if (cost > best || dfs_cnt > MAX_DFS) {
        return;
    }
    int pre[V_SIZE];
    int vs_list[200];
    memset(vs_list, 0xff, sizeof(vs_list));
    int vs_size = 0;

    dfs_cnt++;
    find_path_bfs(u, pre);
    int v;
    for (int i = 0; i < max_cut; i++) {
        v = cut[i].tail;
        if (!path_vis[v]) {
            if (!visited[v]) {
                return;
            }
            else {
                if (v == dst && dep + 1 < max_cut)
                    continue;
                if (pre[v] >= 0)
                    push(v, vs_list, &vs_size);
            }
        }
    }
    int len;
    int ii;
    int tmp;
    int min;
    while (vs_size > 0) {
        /*if (best < max_cost)
        {
            break;
        }*/
        v = pop(vs_list, &vs_size);
        len = 0;
        ii = v;
        while (ii != u) {
            path_vis[ii] = true;
            next[pre[ii]] = ii;
            min = g[pre[ii]][ii];
            if (g2[pre[ii]][ii] < min) {
                min = g2[pre[ii]][ii];
                g2[pre[ii]][ii] = g[pre[ii]][ii];
                g[pre[ii]][ii] = min;
            }
            len += min;
            ii = pre[ii];
        }
        dfs(get_tail[v], dep + 1, cost + len);
        ii = u;
        while (ii != v) {
            tmp = next[ii];
            next[ii] = -1;
            ii = tmp;
            path_vis[ii] = false;
        }
    }
}

long long int solve(int seq[], bool vis[], struct cutPlace cutlist[], int cnum) {
    memcpy(next, seq, max_v * sizeof(int));
    memcpy(path_vis, vis, max_v * sizeof(bool));
    max_cut = cnum;
    memcpy(cut, cutlist, max_cut * sizeof(struct cutPlace));
    for (int i = 0; i < max_v; i++) {
        get_tail[i] = i;
    }
    for (int i = 0; i < max_cut; i++) {
        path_vis[cut[i].tail] = false;
        get_tail[cut[i].tail] = cut[(i + 1) % max_cut].head;
    }
    get_result();
    long long int sum = 0;
    int k;
    k = get_src(&src, &dst);
    cur = src;
    best = max_cost;
    max_dep = 0;
    cur_cost = 0;
    dfs_cnt = 0;
    dfs(src, 0, 0);
    memcpy(next, &best_path1[0], max_v * sizeof(int));
    memcpy(path_vis, &best_vis1[0], max_v * sizeof(bool));
    // printf("%d\n",sum );
    sum += cur_cost;
    int u, v;
    int min;
    for (int i = 1; i <= max_cut; i++) {
        v = cut[(k + i) % max_cut].tail;
        u = cut[(k + i + 1) % max_cut].head;
        if (!path_vis[v]) {
            next[cur] = v;
            path_vis[v] = true;
            min = g[cur][v];
            if (g2[cur][v] < min) {
                min = g2[cur][v];
                g2[cur][v] = g[cur][v];
                g[cur][v] = min;
            }
            sum += min;
            best = max_cost;
            cur_cost = 0;
            cur = u;
            dfs(u, max_dep + 1, 0);
            memcpy(next, &best_path1[0], max_v * sizeof(int));
            memcpy(path_vis, &best_vis1[0], max_v * sizeof(bool));
            sum += cur_cost;
        }
    }

    return sum;
}
//--------------find 1 ----------------//


//--------------find 2 ----------------//
void find_path_bfs2(int begin, int pre[]) {
    //memset(dist, 0, sizeof(dist));
    //memset(queue, 0, sizeof(queue));
    //memset(visited, 0, sizeof(visited));
    //memset(pre, 0xff, sizeof(dist));
    for (int i = 0; i < max_v; i++) {
        dist[i] = 0;
        queue[i + i] = -1;
        queue[i + i + 1] = -1;
        visited[i] = 0;
        pre[i] = -1;
    }
    head = 0;
    tail = 0;
    int u, v;
    int len = adj[begin][0];
    for (int i = 1; i <= len; i++) {
        v = adj[begin][i];
        if (!path_vis[v]) {
            queue[tail] = v;
            pre[v] = begin;
            dist[v] = 1;
            visited[v] = true;
            tail = (tail + 1) % (2 * max_v);
        }
    }
    while (head != tail) {
        u = queue[head];
        head = (head + 1) % (2 * max_v);
        if (u == dst)
            continue;
        u = get_tail[u];
        len = adj[u][0];
        for (int i = 1; i <= len; i++) {
            v = adj[u][i];
            if (!visited[v] && !path_vis[v]) {
                if (pre[u] >= 0 && !isVspec2[u])    //22222222222222
                    pre[v] = u;
                visited[v] = true;
                queue[tail] = v;
                dist[v] = dist[u] + 1;
                tail = (tail + 1) % (2 * max_v);
            }
        }
    }
}

int best_path2[V_SIZE];
bool best_vis2[V_SIZE];

void get_result2() {
    memcpy(&best_path2[0], &next[0], max_v * sizeof(int));
    memcpy(&best_vis2[0], &path_vis[0], max_v * sizeof(bool));
}

void dfs2(int u, int dep, int cost) {
    if (dep > max_dep || (u == src && dep == max_cut && cost < best)) {
        cur = u;
        cur_cost = cost;
        max_dep = dep;
        get_result2();
        if (u == src && dep == max_cut) {
            best = cost;
            cur_cost = best;
            //printf("%d\n", best);
            return;
        }
    }
    if (cost > best || dfs_cnt > MAX_DFS) {
        return;
    }
    int pre[V_SIZE];
    int vs_list[200];
    memset(vs_list, 0xff, sizeof(vs_list));
    int vs_size = 0;

    dfs_cnt++;
    find_path_bfs2(u, pre);
    int v;
    for (int i = 0; i < max_cut; i++) {
        v = cut[i].tail;
        if (!path_vis[v]) {
            if (!visited[v]) {
                return;
            }
            else {
                if (v == dst && dep + 1 < max_cut)
                    continue;
                if (pre[v] >= 0)
                    push(v, vs_list, &vs_size);
            }
        }
    }
    int len;
    int ii;
    int tmp;
    int min;
    while (vs_size > 0) {
        /*if (best < max_cost)
        {
            break;
        }*/
        v = pop(vs_list, &vs_size);
        len = 0;
        ii = v;
        while (ii != u) {
            path_vis[ii] = true;
            next[pre[ii]] = ii;
            min = g[pre[ii]][ii];
            if (g2[pre[ii]][ii] < min) {
                min = g2[pre[ii]][ii];
                g2[pre[ii]][ii] = g[pre[ii]][ii];
                g[pre[ii]][ii] = min;
            }
            len += min;
            ii = pre[ii];
        }
        dfs2(get_tail[v], dep + 1, cost + len);
        ii = u;
        while (ii != v) {
            tmp = next[ii];
            next[ii] = -1;
            ii = tmp;
            path_vis[ii] = false;
        }
    }
}

long long int solve2(int seq[], bool vis[], struct cutPlace cutlist[], int cnum) {
    memcpy(next, seq, max_v * sizeof(int));
    memcpy(path_vis, vis, max_v * sizeof(bool));
    max_cut = cnum;
    memcpy(cut, cutlist, max_cut * sizeof(struct cutPlace));
    for (int i = 0; i < max_v; i++) {
        get_tail[i] = i;
    }
    for (int i = 0; i < max_cut; i++) {
        path_vis[cut[i].tail] = false;
        get_tail[cut[i].tail] = cut[(i + 1) % max_cut].head;
    }
    get_result2();
    long long int sum = 0;
    int k;
    k = get_src(&src, &dst);
    cur = src;
    best = max_cost;
    max_dep = 0;
    cur_cost = 0;
    dfs_cnt = 0;
    dfs2(src, 0, 0);
    memcpy(next, &best_path2[0], max_v * sizeof(int));
    memcpy(path_vis, &best_vis2[0], max_v * sizeof(bool));
    sum += cur_cost;
    int u, v;
    int min;
    for (int i = 1; i <= max_cut; i++) {
        v = cut[(k + i) % max_cut].tail;
        u = cut[(k + i + 1) % max_cut].head;
        if (!path_vis[v]) {
            next[cur] = v;
            path_vis[v] = true;
            min = g[cur][v];
            if (g2[cur][v] < min) {
                min = g2[cur][v];
                g2[cur][v] = g[cur][v];
                g[cur][v] = min;
            }
            sum += min;
            best = max_cost;
            cur_cost = 0;
            cur = u;
            dfs2(u, max_dep + 1, 0);
            memcpy(next, &best_path2[0], max_v * sizeof(int));
            memcpy(path_vis, &best_vis2[0], max_v * sizeof(bool));
            sum += cur_cost;
        }
    }

    return sum;
}
//--------------find 2 ----------------//
//-------------------------------------------find path--------------------------------------//









void UpdateG(int* v_next) {
    int begin = v_next[s];
    int u = begin;
    int v = v_next[u];
    do {
        if (u != t) {
            g[u][v] += INF_REUSE;
        }
        u = v;
        v = v_next[u];
    } while (u != begin);
}

void RestoreG(int* v_next) {
    int begin = v_next[s];
    int u = begin;
    int v = v_next[u];
    do {
        if (u != t) {
            if (g[u][v] > INF_REUSE && g[u][v] < INF) {
                g[u][v] -= INF_REUSE;
            }
            else if (g2[u][v] > INF_REUSE && g2[u][v] < INF){
                g2[u][v] -= INF_REUSE;
            }
        }
        u = v;
        v = v_next[u];
    } while (u != begin);
}



//-----------------------init && lib func below--------------------------------------//
int CFII_init_st_path(TSP *tsp){
    int i;
    int pre, next;

    int  *cnt_arc = tsp->cnt_arc;
    int  *iorder1 = tsp->iorder1;
    int  *iorder2 = tsp->iorder2;
    bool *isVisted1 = tsp->isVisted1;
    bool *isVisted2 = tsp->isVisted2;

    /*init iorder1*/
    pre = s;    
    for (i = 0; i < max_vs1; ++i) {
        next = spec1[i];
        iorder1[pre] = next;
        isVisted1[pre] = true;
        if (data[pre][next] > 0) {
            cnt_arc[data[pre][next]] ++;
        }
        pre = next;
    }
    iorder1[pre] = t;
    iorder1[t] = s;
    isVisted1[pre] = true;
    isVisted1[t] = true;

    /*init iorder2*/
    pre = s;    
    for (i = 0; i < max_vs2; ++i) {
        next = spec2[i];
        iorder2[pre] = next;
        isVisted2[pre] = true;
        if (data[pre][next] > 0) {
            cnt_arc[data[pre][next]] ++;
        }
        pre = next;
    }
    iorder2[pre] = t;
    iorder2[t] = s;
    isVisted2[pre] = true;
    isVisted2[t] = true;

    return 0;
}

long long int CFII_get_singlePath_Length(int *iorder) {
    long long int len = 0;
    int pre, next;

    pre = s;
    next = iorder[pre];    
    while(pre != t /*&& next != -1*/) {
        len += g[pre][next];
        pre = next;
        next = iorder[next];
    }
    return len;
}

long long int CFII_getTotal_Length_with_Reused(TSP *tsp)
{
    long long int len = 0;
    int pre, next;
    int edge_id;

    int  *iorder1 = tsp->iorder1;
    int  *iorder2 = tsp->iorder2;


    pre = s;
    next = iorder1[pre];    
    while(pre != t) {
        len += g[pre][next];
        edgesCount[data[pre][next]]++;
        pre = next;
        next = iorder1[next];
    }

    pre = s;    
    next = iorder2[pre];    
    while(pre != t) {
        edge_id = data[pre][next];
        if ( edgesCount[edge_id]>0)
        {
            if (data2[pre][next] > 0) {
                len += g2[pre][next];
            }
            else {
                len += g[pre][next];
                len += INF_REUSE;
            }
        }
        else{
            len += g[pre][next];
        }
        pre = next;
        next = iorder2[next];
    }

    pre = s;
    next = iorder1[pre];    
    while(pre != t) {
        edgesCount[data[pre][next]]--;
        pre = next;
        next = iorder1[next];
    }

    return len;
}


void CFII_write_Order_to_path(int *iorder, int *topath){
    /*write result to path[1]*/
    // memset(path1, 0, sizeof(path1));
    
    int next = s;
    topath[0] = 0;
    while(next != t || next < 0){
        topath[topath[0]+1] = next;
        topath[0]++;
        next = iorder[next];
    }
    topath[topath[0]+1] = next;
    topath[0]++;
    return;
}


int CFII_getReuseEdges(int *iorder1, int *iorder2){
    int cnt = 0;
    int edge_id;

    int pre = s;
    int next = iorder1[pre];
    while(pre != t) {
        edge_id = data[pre][next];
        edgesCount[edge_id]++;
        pre = next;
        next = iorder1[next];
    }

    pre = s;
    next = iorder2[pre];
    while(pre != t) {
        edge_id = data[pre][next];
        if (edgesCount[edge_id]>0) {
            if (data2[pre][next] < 0)
            {
                cnt++;                
            }
        }
        pre = next;
        next = iorder2[next];
    }

    pre = s;
    next = iorder1[pre];
    while(pre != t) {
        edge_id = data[pre][next];
        edgesCount[edge_id]--;
        pre = next;
        next = iorder1[next];
    }

    return cnt;
}

//-----------------------init && lib func above--------------------------------------//





//-----------------------------debug functions below---------------------------------//
void DBG_CFII_print_iorder(TSP *tsp){
    int pre;
    int cnt;
    int  *iorder1 = tsp->iorder1;
    int  *iorder2 = tsp->iorder2;

    int weight = 0;

    printf("@DBG_print_iorder:\niorder1:");
    cnt = 1;
    pre = s; 
    while(iorder1[pre] != t /*&& iorder1[pre] > 0*/) {
        printf(" %d", pre);
        if (isVspec1[pre])
        {
            printf("(%d)", cnt++);
        }
        if (data[pre][iorder1[pre]] < 0 )
        {
            printf("!!!(%d,%d)!!!", pre, iorder1[pre] );
        }
        printf("\n---[%d]%d---", g[pre][iorder1[pre]], data[pre][iorder1[pre]]);
        weight += g[pre][iorder1[pre]];
        edgesCount[data[pre][iorder1[pre]]]++;
        pre = iorder1[pre];
    }
    printf(" %d", pre);
    if (isVspec1[pre])
        printf("(%d)", cnt++);
    printf(" %d(%d)\n", iorder1[pre], cnt );
    printf(" weight iorder1 = %d\n", weight);

    printf("iorder2:");
    weight = 0;
    cnt = 1;
    pre = s; 
    while(iorder2[pre] != t /*&& iorder2[pre] > 0*/) {
        printf(" %d", pre);
        if (isVspec2[pre])
        {
            printf("(%d)", cnt++);
        }
        printf("\n---[%d]%d---", g[pre][iorder2[pre]], data[pre][iorder2[pre]] );
        weight += g[pre][iorder2[pre]];
        if (edgesCount[data[pre][iorder2[pre]]])
        {
            printf("!!!REUSED ID=%d!!!", data[pre][iorder2[pre]] );
            if(data2[pre][iorder2[pre]] > 0){
                printf("###NOT Really ReID=%d###", data2[pre][iorder2[pre]]);
            }
        }
        pre = iorder2[pre];
    }
    printf(" %d", pre);
    if (isVspec2[pre])
        printf("(%d)", cnt++);
    printf(" %d(%d)\n", iorder2[pre], cnt );
    printf(" weight iorder2 = %d\n", weight);


    /* RE do edgeCunt change*/
    pre = s; 
    while(iorder1[pre] != t /*&& iorder1[pre] > 0*/) {
        edgesCount[data[pre][iorder1[pre]]]--;
        pre = iorder1[pre];
    }
    return;
}
//-----------------------------debug functions above---------------------------------//







//*******************************************************************************************************//
//******************************************   N-opt   **************************************************//
//*******************************************************************************************************//
//-----------------------------N-opt functions below---------------------------------//
// int count_flag;
// int xx = 0;

int cut_low;
int min_cut;
int cut_len;
int get_max_cutnum(int max_vs, int unconnect){
    int Max_cut;

    if (AS_max_cut_num > 10) {
        return AS_max_cut_num - 10 + unifRand(10);
    }
    if (unconnect > cut_low){
        //return unconnect - 1;
        Max_cut = min_cut + unifRand(cut_len);
        if (Max_cut > max_vs + 1) {
            Max_cut = max_vs + 1;
        }
    }

    else if (max_vs > 10) {
        if (max_v > 1500) {

            Max_cut = 3 + unifRand(3);            
        }
        else if (max_v >= 990) {
            Max_cut = 5 + unifRand(4);    
        }
        else if (max_v > 500) {
            Max_cut = 5 + unifRand(5);  
        }
        else if (max_v > 200) {
            Max_cut = 6 + unifRand(6);
        }
        else {
            Max_cut = 6 + unifRand(8); 
        }
    }
    else if(max_vs > 0) {
        Max_cut = max_vs + 1;
    }
    else if (max_vs == 0) {
        Max_cut = 1;
    }
    return Max_cut;
}

int buff_iorder[V_SIZE];
bool buff_vis[V_SIZE];
long long int CFII_cut_naive1(TSP *tsp ,struct cutPlace *cut_rcd, int *cut_num) {

    int MAX_cut_numbers;

    memcpy(&buff_iorder[0], tsp->iorder1, max_v * sizeof(int));
    memcpy(&buff_vis[0], tsp->isVisted1, max_v * sizeof(bool));

    bool isSelected[108];
    bool isCountedVs[2008];
    bool isHead[2008];
    bool isTail[2008];
    memset(isSelected, 0, sizeof(isSelected));
    memset(isCountedVs, 0, sizeof(isCountedVs));
    memset(isTail, 0, sizeof(isTail));
    memset(isHead, 0, sizeof(isHead));


    long long int len = 0;
    int edge_id;
    int head_index = 1;
    int c_next;
    int count;
    int head_tmp;
    // DBG_CFII_print_iorder(tsp);
    
    int  pre, next, pre_vs;
    int unconne_vs_cnt = 0;

    /* 1.0 Count all the unconnected node and mark it*/
      /* 1.0-1 SITUATION: HAVE GOT RESULT !!! */
    if (tsp->best_len1 < INF) {
        /*get reused vs numbers and mark it node*/
        pre = s;
        next = tsp->iorder2[pre];
        while(pre != t) { //record tsp->iorder2 to edgesCount
            edge_id = data[pre][next];
            edgesCount[edge_id]++;
            pre = next;
            next = tsp->iorder2[next];
        }

        pre = s;
        next = buff_iorder[pre];
        while(pre != t) { //count reused vs1 nodes to unconne_vs_cnt
            if (isVspec1[pre]) {
                pre_vs = pre;
            }
            edge_id = data[pre][next];
            if (edgesCount[edge_id] > 0 && !isCountedVs[pre_vs]) {
                if (data2[pre][next] < 0) 
                {
                    isCountedVs[pre_vs] = 1;
                    unconne_vs_cnt++;
                }
            }
            pre = next;
            next = buff_iorder[next];
        }

        pre = s;
        next = tsp->iorder2[pre];
        while(pre != t) { //delete edgesCount of tsp->iorder2
            edge_id = data[pre][next];
            edgesCount[edge_id]--;
            pre = next;
            next = tsp->iorder2[next];
        }
    } /* 1.0-2 SITUATION: NO RESULT !!! */
    else {
        /*get unconnected vs numbers and mark it node*/
        pre = s;
        next = buff_iorder[pre];
        while ( pre != t ) {
            if (isVspec1[pre]) {
                pre_vs = pre;
            }
            if (g[pre][next] == INF && !isCountedVs[pre_vs]) {
                unconne_vs_cnt++;
                isCountedVs[pre_vs] = 1;
            }
            pre = next;
            next = buff_iorder[next];
        }
    }

    MAX_cut_numbers = get_max_cutnum(max_vs1, unconne_vs_cnt);
    
    /* 2 get all the head*/
    /* 2.1 if MAX_cut_numbers is less than unconnected vsnode
     * we just get the fisrt max_cut numbers unconnected point*/
    if (unconne_vs_cnt >= MAX_cut_numbers)
    { 
        count = 0;
        pre = s;
        while (count < MAX_cut_numbers) {
            /*get vailid head index*/
            if (isVspec1[pre] && isCountedVs[pre] ) //22222222222222222
            {
                isHead[pre] = true;
                count = count + 1;
            }
            pre = buff_iorder[pre];
        }
    }
        /* 2.2 if MAX_cut_numbers is more than unconnected vsnode
         * we first get unconne_vs_cnt cut segs
         *     then randome get rand_cut_num cut segs*/
    else {
        int rand_cut_num = MAX_cut_numbers - unconne_vs_cnt;

        /*First get unconne_vs_cnt cut segs*/
        pre = s;
        while ( pre != t ) {
            if (isVspec1[pre] && isCountedVs[pre] )
            {
                isHead[pre] = true;
            }
            pre = buff_iorder[pre];
        }

        /*Seecondly, randome get rand_cut_num cut segs*/
        count = 0;
        while (count < rand_cut_num) {
            /*get vailid head index*/
            do {
                head_index = unifRand(max_vs1 + 1);
                // printf(" %d\t\t\t", head_index);
            } while (isSelected[head_index] || isHead[spec1[head_index]]);
            isSelected[head_index] = true;

            /*get cut_rcd->head*/
            head_tmp = spec1[head_index];
            isHead[head_tmp] = true;
            count = count + 1;
        }
    }

    

    /* 3.0 get all the head, tail and cut length*/
    count = 0;
    int id = s;
    while (count < MAX_cut_numbers) {
        if (isHead[id]) {
            /*record cut_rcd->head*/
            cut_rcd[count].head = id;
            //if (id == 55)
            //  printf("get 55\n");
            /*add the cut_rcd length*/
            head_tmp = id;
            c_next = buff_iorder[head_tmp];
            len += g[head_tmp][c_next];
            while (!isVspec1[c_next]) {
                head_tmp = c_next;
                c_next = buff_iorder[c_next];
                len += g[head_tmp][c_next];
            }
            cut_rcd[count].tail = c_next;
            count = count + 1;
        }
        id = buff_iorder[id];
    }


    // DBG_CFII_print_iorder(tsp);
    /* 4.0 cut_rcd all the cutPlaces*/
    for (int i = 0; i < MAX_cut_numbers; ++i) {
        /*cut_rcd order*/
        head_tmp = cut_rcd[i].head;
        c_next = buff_iorder[head_tmp];
        while (!isVspec1[c_next]) {
            buff_iorder[head_tmp] = -1;
            buff_vis[c_next] = false;
            head_tmp = c_next;
            c_next = buff_iorder[c_next];
        }
        buff_iorder[head_tmp] = -1;
    }

    *cut_num = MAX_cut_numbers;
    return len;
}


long long int CFII_cut_naive2(TSP *tsp ,struct cutPlace *cut_rcd, int *cut_num) {

    int MAX_cut_numbers;

    memcpy(&buff_iorder[0], tsp->iorder2, max_v * sizeof(int));
    memcpy(&buff_vis[0], tsp->isVisted2, max_v * sizeof(bool));

    bool isSelected[108];
    bool isCountedVs[2008];
    bool isHead[2008];
    bool isTail[2008];
    memset(isSelected, 0, sizeof(isSelected));
    memset(isCountedVs, 0, sizeof(isCountedVs));
    memset(isTail, 0, sizeof(isTail));
    memset(isHead, 0, sizeof(isHead));


    long long int len = 0;
    int edge_id;
    int head_index = 1;
    int c_next;
    int count;
    int head_tmp;
    
    // DBG_CFII_print_iorder(tsp);
    
    /*1.0 count all the unconnect or reused vs number*/
    int  pre, next, pre_vs;
    int unconne_vs_cnt = 0;

    /*1.0-1 SITUATION: HAVE GOT RESULT !!! */
    if (tsp->best_len2 < INF) {
        /*get reused vs numbers and mark it node*/
        pre = s;
        next = tsp->iorder1[pre];
        while(pre != t) { //record tsp->iorder2 to edgesCount
            edge_id = data[pre][next];
            edgesCount[edge_id]++;
            pre = next;
            next = tsp->iorder1[next];
        }

        pre = s;
        next = buff_iorder[pre];
        while(pre != t) { //count reused vs1 nodes to unconne_vs_cnt
            if (isVspec2[pre]) {
                pre_vs = pre;
            }
            edge_id = data[pre][next];
            if (edgesCount[edge_id] > 0 && !isCountedVs[pre_vs]) {
                if (data2[pre][next] < 0) 
                {
                    isCountedVs[pre_vs] = 1;
                    unconne_vs_cnt++;
                }
            }
            pre = next;
            next = buff_iorder[next];
        }

        pre = s;
        next = tsp->iorder1[pre];
        while(pre != t) { //delete edgesCount of tsp->iorder2
            edge_id = data[pre][next];
            edgesCount[edge_id]--;
            pre = next;
            next = tsp->iorder1[next];
        }
    }
    /*1.0-2 SITUATION: NO RESULT !!! */
    else {
        /*get unconnected vs numbers and mark it node*/
        pre = s;
        next = buff_iorder[pre];
        while ( pre != t ) {
            if (isVspec2[pre]) {
                pre_vs = pre;
            }
            if (g[pre][next] == INF && !isCountedVs[pre_vs]) {
                unconne_vs_cnt++;
                isCountedVs[pre_vs] = 1;
            }
            pre = next;
            next = buff_iorder[next];
        }
    }

    MAX_cut_numbers = get_max_cutnum(max_vs2, unconne_vs_cnt);

    /* 2 get all the head*/
    /* 2.1 if MAX_cut_numbers is less than unconnected vsnode
     * we just get the fisrt max_cut numbers unconnected point*/
    if (unconne_vs_cnt >= MAX_cut_numbers)
    { 
        count = 0;
        pre = s;
        while (count < MAX_cut_numbers) {
            /*get vailid head index*/
            if (isVspec2[pre] && isCountedVs[pre] ) //22222222222222222
            {
                isHead[pre] = true;
                count = count + 1;
            }
            pre = buff_iorder[pre];
        }
    }
        /* 2.2 if MAX_cut_numbers is more than unconnected vsnode
         * we first get unconne_vs_cnt cut segs
         * then randome get rand_cut_num cut segs*/
    else {
        int rand_cut_num = MAX_cut_numbers - unconne_vs_cnt;

        /*First get unconne_vs_cnt cut segs*/
        pre = s;
        while ( pre != t ) {
            if (isVspec2[pre] && isCountedVs[pre] )
            {
                isHead[pre] = true;
            }
            pre = buff_iorder[pre];
        }

        /*Seecondly, randome get rand_cut_num cut segs*/
        count = 0;
        while (count < rand_cut_num) {
            /*get vailid head index*/
            do {
                head_index = unifRand(max_vs2 + 1);
                // printf(" %d\t\t\t", head_index);
            } while (isSelected[head_index] || isHead[spec2[head_index]]);
            isSelected[head_index] = true;

            /*get cut_rcd->head*/
            head_tmp = spec2[head_index];
            isHead[head_tmp] = true;
            count = count + 1;
        }
    }


    /* 3.0 get all the head, tail and cut length*/
    count = 0;
    int id = s;
    while (count < MAX_cut_numbers) {
        if (isHead[id]) {
            /*record cut_rcd->head*/
            cut_rcd[count].head = id;
            //if (id == 55)
            //  printf("get 55\n");
            /*add the cut_rcd length*/
            head_tmp = id;
            c_next = buff_iorder[head_tmp];
            len += g[head_tmp][c_next];
            while (!isVspec2[c_next]) {
                head_tmp = c_next;
                c_next = buff_iorder[c_next];
                len += g[head_tmp][c_next];
            }
            cut_rcd[count].tail = c_next;
            count = count + 1;
        }
        id = buff_iorder[id];
    }

    // printf("<<<<: print iorder1\n");
    // DBG_CFII_print_iorder(tsp);
    


    /* 4.0 cut_rcd all the cutPlaces*/
    for (int i = 0; i < MAX_cut_numbers; ++i) {
        /*cut_rcd order*/
        head_tmp = cut_rcd[i].head;
        c_next = buff_iorder[head_tmp];
        while (!isVspec2[c_next]) {
            buff_iorder[head_tmp] = -1;
            buff_vis[c_next] = false;
            head_tmp = c_next;
            c_next = buff_iorder[c_next];
        }
        buff_iorder[head_tmp] = -1;
    }

    *cut_num = MAX_cut_numbers;
    return len;
}



int CFII_tryNopt_for1(TSP *tsp, long long int *pathlen, int *pathchg, double T) {

    /*init*/
    long long int energyChange = 0;
    long long int en_before;
    long long int en_later;

    int cut_num = 0;

    struct cutPlace cut[MAX_CUT_NUM];
    memset(cut, 0, sizeof(cut));

    /*get cut1 info and cut iorder1*/
    en_before = CFII_cut_naive1(tsp, cut, &cut_num);
    /*reconnect iorder1*/
    en_later = solve(buff_iorder, buff_vis, cut, cut_num);
    energyChange += en_later - en_before;
    // printf("en_before=%lld, en_later=%lld\n", en_before, en_later);

    if (energyChange < 0 || PARA_02 < exp(-energyChange / T)) {
        *pathchg =  *pathchg + 1;
        memcpy(tsp->iorder1, &best_path1[0], max_v * sizeof(int));
        memcpy(tsp->isVisted1, &best_vis1[0], max_v * sizeof(bool));
        *pathlen = CFII_get_singlePath_Length(tsp->iorder1);          
    }
    return 0;
};


int CFII_tryNopt_for2(TSP *tsp, long long int *pathlen, int *pathchg, double T) {

    /*init*/
    long long int energyChange = 0;
    long long int en_before;
    long long int en_later;

    int cut_num = 0;

    struct cutPlace cut[MAX_CUT_NUM];
    memset(cut, 0, sizeof(cut));

    /*get cut2 info and cut iorder1*/
    en_before = CFII_cut_naive2(tsp, cut, &cut_num);
    /*reconnect iorder2*/
    en_later = solve2(buff_iorder, buff_vis, cut, cut_num);
    energyChange += en_later - en_before;

    if (energyChange < 0 || PARA_02 < exp(-energyChange / T)) {
        *pathchg = *pathchg + 1;
        memcpy(tsp->iorder2, &best_path2[0], max_v * sizeof(int));
        memcpy(tsp->isVisted2, &best_vis2[0], max_v * sizeof(bool));

        *pathlen = CFII_get_singlePath_Length(tsp->iorder2);
    }
    return 0;
};


int CFII_tryNopt(TSP *tsp, long long int *pathlen, int *pathchg, double T) {

    /*init*/
    long long int energyChange = 0;
    int en_before;
    int en_later;

    int reused_before;
    int reused_later;

    int cut_num = 0;

    struct cutPlace cut[MAX_CUT_NUM];
    memset(cut, 0, sizeof(cut));
    reused_before = tsp->reused_num;

    /*get cut1 info and cut iorder1*/
    en_before = CFII_cut_naive1(tsp, cut, &cut_num);
    /*reconnect iorder1*/
    en_later = solve(buff_iorder, buff_vis, cut, cut_num);
    energyChange += en_later - en_before;

    /*get cut2 info and cut iorder2*/
    en_before = CFII_cut_naive2(tsp, cut, &cut_num);
    /*reconnect iorder2*/
    en_later = solve2(buff_iorder, buff_vis, cut, cut_num);
    energyChange += en_later - en_before;

    reused_later = CFII_getReuseEdges(&best_path1[0], &best_path2[0]);
    energyChange += INF_REUSE * (reused_later - reused_before);


    if (energyChange < 0 || PARA_02 < exp(-energyChange / T)) {
        *pathchg = *pathchg + 1;
        memcpy(tsp->iorder1, &best_path1[0], max_v * sizeof(int));
        memcpy(tsp->isVisted1, &best_vis1[0], max_v * sizeof(bool));
        memcpy(tsp->iorder2, &best_path2[0], max_v * sizeof(int));
        memcpy(tsp->isVisted2, &best_vis2[0], max_v * sizeof(bool));

        tsp->reused_num = reused_later;
        // tsp->best_len1 = CFII_get_singlePath_Length(tsp->iorder1, reused_later);
        // tsp->best_len2 = CFII_get_singlePath_Length(tsp->iorder2, reused_later);
        // *pathlen = CFII_getTotal_Length_with_Reused(tsp);
        // *pathlen = tsp->best_len1 + tsp->best_len2;

        // if (reused_later > 0) {            
        //     printf(" reused_later = %d\n", reused_later);
        // }
        // *pathlen += energyChange; 
    }
    // printf("%d\n", *pathlen);
    return 0;
};
//-----------------------------N-opt functions above---------------------------------//









//*******************************************************************************************************//
//******************************************   Annealing   **********************************************//
//*******************************************************************************************************//
//----------- AS solution lib function below--------------//
void annealing_vs1(TSP *tsp)
{

    int    pathchg, nochgtimes;
    long long int    pathlen;
    int    *iorder1 = tsp->iorder1;
    double T;

    tsp->best_len1 = CFII_get_singlePath_Length(tsp->iorder1);
    pathlen = tsp->best_len1;

    tsp->bestlen = pathlen;
    nochgtimes   = 0;
    AS_max_cut_num  = max_vs1;

    for (T = AS_T_INIT; T > AS_FINAL_T; T *= AS_COOLING)  /* annealing schedule */
    {
        pathchg = 0;
        for (int j = 0; j < AS_TRIES_PER_T_for_init; j++)
        {

            CFII_tryNopt_for1(tsp, &pathlen, &pathchg, T);       
            if ( pathlen < (tsp->best_len1) ) {
                tsp->best_len1 = pathlen;
                CFII_write_Order_to_path(iorder1, &path1[0]);
                if (pathlen < INF) {
                    return;
                }
            }
            if (pathchg > AS_IMPROVED_PATH_PER_T) break; /* finish early */
        }   
        // DBG("T:%5f L:%lld B:%lld C:%d Len1:%lld Len2:%lld\n", T, pathlen, tsp->bestlen, pathchg, tsp->best_len1, tsp->best_len2);
        AS_max_cut_num = AS_max_cut_num/2;
        if (pathchg == 0) nochgtimes++;
        if (nochgtimes == AS_no_change_time_for_init) break;
    }
    printf("    !!!!!!!NOT get Path1, pathlen = %lld!!!!!!!!\n", pathlen);
    return;
}

void annealing_vs2(TSP *tsp)
{
    int    pathchg, nochgtimes;
    long long int    *pathlen;
    int    *iorder2 = tsp->iorder2;
    double T;
    pathlen  = (long long int *) malloc(sizeof(long long int));

    tsp->best_len2 = CFII_get_singlePath_Length(tsp->iorder2);
    *pathlen = tsp->best_len2;

    tsp->bestlen = *pathlen;
    nochgtimes   = 0;
    AS_max_cut_num  = max_vs2;

    for (T = AS_T_INIT; T > AS_FINAL_T; T *= AS_COOLING)  /* annealing schedule */
    {
        pathchg = 0;
        for (int j = 0; j < AS_TRIES_PER_T_for_init; j++)
        {
            CFII_tryNopt_for2(tsp, pathlen, &pathchg, T);
            if ( *pathlen < (tsp->best_len2) ) {
                tsp->best_len2 = *pathlen;
                CFII_write_Order_to_path(iorder2, &path2[0]);
                if (*pathlen < INF) {                   
                    free(pathlen);
                    return;
                }
            }
            if (pathchg > AS_IMPROVED_PATH_PER_T) break; /* finish early */
        }   
        // DBG("T:%5f L:%lld B:%ld C:%d Len1:%lld Len2:%lld\n", T, *pathlen, tsp->bestlen, pathchg, tsp->best_len1, tsp->best_len2);
        AS_max_cut_num = AS_max_cut_num/2;
        if (pathchg == 0) nochgtimes++;
        if (nochgtimes == AS_no_change_time_for_init) break;
    }
    printf("    !!!!!!!NOT get Path2, pathlen = %lld!!!!!!!!\n", *pathlen);
    return;
}




void annealing(TSP *tsp)
{

    int    pathchg, nochgtimes;
    long long int    *pathlen;
    int    *iorder1 = tsp->iorder1;
    int    *iorder2 = tsp->iorder2;
    double T;
    pathlen  = (long long int *) malloc(sizeof(long long int));

    // tsp->best_len1 = CFII_get_singlePath_Length(tsp->iorder1, tsp->reused_num);
    // tsp->best_len2 = CFII_get_singlePath_Length(tsp->iorder2, tsp->reused_num);
    // *pathlen = tsp->best_len1 + tsp->best_len2;
    *pathlen = CFII_getTotal_Length_with_Reused(tsp);

    // tsp->bestlen = *pathlen;
    tsp->best_len1 = *pathlen;
    tsp->best_len2 = *pathlen;
    nochgtimes   = 0;

    // printf("init len1 = %lld, init len2 = %lld\n",tsp->best_len1, tsp->best_len2 );
    // printf("INIT Path Length       : %lld, reused=%d\n", *pathlen, tsp->reused_num);
    // DBG_CFII_print_iorder(tsp);

    unsigned int it_cnt = 1;
    AS_max_cut_num = -1;
    for (T = AS_T_INIT; T > AS_FINAL_T; T *= AS_COOLING)  /* annealing schedule */
    {
        pathchg = 0;
        for (int j = 0; j < AS_TRIES_PER_T; j++)
        {

            if (it_cnt % 2 == 0) {
                UpdateG(tsp->iorder2);
                CFII_tryNopt_for1(tsp, pathlen, &pathchg, T);
                RestoreG(tsp->iorder2);
                if ( *pathlen < (tsp->best_len1) ) {
                    tsp->best_len1 = *pathlen;
                    CFII_write_Order_to_path(iorder1, &path1[0]);
                    // CFII_write_Order_to_path(iorder2, &path2[0]);
                    // DBG_CFII_print_iorder(tsp);
                }
            }
            else {
                UpdateG(tsp->iorder1);
                CFII_tryNopt_for2(tsp, pathlen, &pathchg, T);
                RestoreG(tsp->iorder1);
                if ( *pathlen < (tsp->best_len2) ) {
                    tsp->best_len2 = *pathlen;
                    CFII_write_Order_to_path(iorder2, &path2[0]);
                    // CFII_write_Order_to_path(iorder1, &path1[0]);
                    // DBG_CFII_print_iorder(tsp);
                }
            }
            if (pathchg > AS_IMPROVED_PATH_PER_T) break; /* finish early */
        }
        it_cnt++;
        // DBG("T:%5f L:%lld B:%lld C:%d Len1:%lld Len2:%lld\n", T, *pathlen, tsp->bestlen, pathchg, tsp->best_len1, tsp->best_len2);

        gettimeofday(&end_time, NULL);
        duration = 1000*(end_time.tv_sec - begin_time.tv_sec) + 0.001*(end_time.tv_usec - begin_time.tv_usec);
        duration = duration/1000;
        // printf("time = %.3f s\n",duration/1000);
        if (duration > 8.00)  return;
        if (pathchg == 0) nochgtimes++;
        if (nochgtimes == AS_no_change_time) break;
    }
    // printf("it_cnt = %d\n", it_cnt);
    return;
}




//*******************************************************************************************************//
//*******************************************************************************************************//
//*******************************************************************************************************//

/* INIT TSP DATA*/
int find_Craft_solution(int n, int start, int end, long long int *res)
{
    TSP   tsp; 

    /*init random function*/
    initRand(AS_seed);
    srand(AS_seed);

    /*initialize tsp struct*/
    tsp.bestlen = 1000000000;

    tsp.cnt_arc        = NULL;
    tsp.reused_num     = 0;
    tsp.tmp_reused_num = 0;

    tsp.best_len1 = 0;
    tsp.iorder1       = NULL;
    tsp.isVisted1     = NULL;

    tsp.best_len2 = 0;
    tsp.iorder2       = NULL;
    tsp.isVisted2     = NULL;


    if (!(tsp.cnt_arc = (int*) malloc (max_e * sizeof(int)))              ||
        !(tsp.iorder1      = (int*) malloc (max_v * sizeof(int)))         ||        
        !(tsp.isVisted1    = (bool *) malloc (max_v * sizeof(bool)))      ||

        !(tsp.iorder2      = (int*) malloc (max_v * sizeof(int)))         ||
        !(tsp.isVisted2    = (bool *) malloc (max_v * sizeof(bool)))       ){
            return -1;
            printf( "Memory allocation failed!");
    }


    memset(tsp.cnt_arc, 0, max_e * sizeof(int));

    memset(tsp.iorder1, 0xff, max_v * sizeof(int));
    memset(tsp.iorder2, 0xff, max_v * sizeof(int));

    memset(tsp.isVisted1, 0, max_v * sizeof(bool));
    memset(tsp.isVisted2, 0, max_v * sizeof(bool));

    memset(path1, 0xff, sizeof(path1));    
    memset(path2, 0xff, sizeof(path2));
    memset(edgesCount, 0, sizeof(edgesCount));

    CFII_init_st_path(&tsp); //init iorder1,iorder2,

    annealing_vs1(&tsp);
    UpdateG(tsp.iorder1);
    annealing_vs2(&tsp);
    RestoreG(tsp.iorder1);

    // *res = CFII_getTotal_Length_with_Reused(&tsp);                 //DBGGG
    // tsp.reused_num = CFII_getReuseEdges(tsp.iorder1, tsp.iorder2); //DBGGG 
    // printf("        SOLUTION INIT len1 = %lld, len2 = %lld\n",tsp.best_len1, tsp.best_len2 );
    // printf("        SOLUTION INIT total_len = %lld, reused=%d\n", *res, tsp.reused_num);

    annealing(&tsp);

    *res = CFII_getTotal_Length_with_Reused(&tsp);

    // tsp.best_len1 = CFII_get_singlePath_Length(tsp.iorder1);
    // tsp.best_len2 = CFII_get_singlePath_Length(tsp.iorder2);

    // tsp.reused_num = CFII_getReuseEdges(tsp.iorder1, tsp.iorder2); //DBGGG 
    // printf("        Final len1 = %lld, len2 = %lld\n",tsp.best_len1, tsp.best_len2 );
    // printf("        Final Path TOTAL Length: %lld, reused=%d\n", *res, tsp.reused_num);
    // DBG_CFII_print_iorder(&tsp);
    return 0;
}
//------------ AS solution lib function above-------------//








//---------------------------IO code below ----------------------------------------//

void CFII_read_topos(char *topo[MAX_EDGE_NUM], int edge_num){
    memset(data, 0xff, sizeof(data));
    memset(data2, 0xff, sizeof(data2));
    memset(w, 0, sizeof(w));
    memset(adj, 0, sizeof(adj));
    // memset(prt, 0, sizeof(prt));
    // memset(g, 0x7f, sizeof(g));
    // memset(g2, 0x7f, sizeof(g2));
    // memset(a, 0, sizeof(a));

    char *input_topo;
    int id;
    int x;
    int y;
    int weight;
    int i, j;
    max_v = 0;
    max_e = 0;
    // read data[][]
    // g[][] = data[][]
    for (i = 0; i < 2008; ++i)
    {
        for (j = 0; j < 2008; ++j)
        {
            g[i][j] = INF;
            g2[i][j] = INF;
        }        
    }
    g[t][s] = 0;

    adj[t][0] = 1;
    adj[t][1] = s;
    for (i = 0; i < edge_num; ++i)
    {
        input_topo = topo[i];
        // printf("%s\n", input_topo );
        sscanf(input_topo, "%d,%d,%d,%d", &id, &x, &y, &weight); 
        if (id + 1 > max_e) max_e = id + 1;
        if (x + 1 > max_v) max_v = x + 1;
        if (y + 1 > max_v) max_v = y + 1;
        if (x != t && y != s) {
            if (data[x][y] < 0) { // first edge
                adj[x][0]++;
                adj[x][adj[x][0]] = y;
                // a[x][y] = 1;
                data[x][y] = id;
                g[x][y] = weight;
            }
            else {
                if (data2[x][y] < 0) { //second edge
                    if (weight < g[x][y]) {
                        data2[x][y] = data[x][y];
                        g2[x][y]    = g[x][y];
                        data[x][y] = id;
                        g[x][y]    = weight;
                    }
                    else{
                        data2[x][y] = id;
                        g2[x][y] = weight;    
                    }
                }
                else {  // third edge comes
                    if (weight < g[x][y])
                    {
                        data2[x][y] = data[x][y];
                        g2[x][y]    = g[x][y];
                        data[x][y] = id;
                        g[x][y]    = weight;
                    }
                    else if (weight < g2[x][y])
                    {
                        data2[x][y] = id;
                        g2[x][y] = weight; 
                    }
                }             
            }
        }
        w[id] = weight;
    }
    return;
}

void CFII_read_demands(char *demand[MAX_DEMAND_NUM], int demand_num){
    max_vs1 = 0;
    max_vs2 = 0;
    memset(spec1, 0, sizeof(spec1));
    memset(spec2, 0, sizeof(spec2));
    memset(isVspec1, 0, sizeof(isVspec1));
    memset(isVspec2, 0, sizeof(isVspec2));

    int offset, x;
    char ch;
    char *demand_data;

    demand_data = demand[0];
    sscanf(demand_data,"%d,%d,%d,%n", &x, &s, &t, &offset);
    demand_data += offset;
    isVspec1[s] = true;
    isVspec1[t] = true;
    // printf("%d,%d,%d,%d\n", x, s, t, offset);

    while ( sscanf(demand_data, "%d%c%n", &x, &ch, &offset) >= 1 ) {
        // printf("%d ", x);
        demand_data += offset;
        isVspec1[x] = true;
        spec1[max_vs1] = x;
        max_vs1++;
    }
    spec1[max_vs1] = s;
    spec1[max_vs1+1] = t;

    demand_data = demand[1];
    sscanf(demand_data,"%d,%d,%d,%n", &x, &s, &t, &offset);
    demand_data += offset;
    isVspec2[s] = true;
    isVspec2[t] = true;
    // printf("\n%d,%d,%d,%d\n", x, s, t, offset);

    while ( sscanf(demand_data, "%d%c%n", &x, &ch, &offset) >= 1 ) {
        // printf("==%d ", x);
        demand_data += offset;
        isVspec2[x] = true;
        spec2[max_vs2] = x;
        max_vs2++;
    }
    spec2[max_vs2] = s;
    spec2[max_vs2+1] = t;
    return;
}

void CFII_print_path_to_results1(long long int res, unsigned short * result1, unsigned short * result2) {
    if (res < INF*2) {
        //printf("result path length = %d\n", best);
        int len = path1[0];
        for (int i = 2; i < len; i++) {
            result1[i-2] = data[path1[i - 1]][path1[i]];
        }
        result1[len-2] = data[path1[len - 1]][path1[len]];

        len = path2[0];
        for (int i = 2; i < len; i++) {
            result2[i-2] = data[path2[i - 1]][path2[i]];
        }
        result2[len-2] = data[path2[len - 1]][path2[len]];
    }
    else {
        printf("NA error\n");
    }
}




void Bfs_for_D_node(int ss , bool* Dnode){
    int counter1 = 0;
    int counter2 = 0;
    int counter = 0;
    int dead_stack[4008];
    bool temp_used[4008];
    int  temp_que[4008];
    memset(temp_used,0,sizeof(temp_used));
    int hh = 0, tt = 1;
    temp_que[hh]=ss;
    temp_used[ss] = 1;
    int node;
    int i;
    while(hh != tt)
    {
        node = temp_que[hh];
        hh = (hh+1)%4008;
        dead_stack[counter] = node;
        counter += 1;
        if(isVspec1[node])
            counter1 += 1;
        if(isVspec2[node])            
            counter2 += 1;
        if(counter1>=max_vs1 || counter2>=max_vs2)
            return;
        for (i = 1; i <= adj[node][0]; ++i)
            if (!temp_used[adj[node][i]] && !Dnode[adj[node][i]])
            {
                temp_que[tt] = adj[node][i];
                tt = (tt+1)%4008;
                temp_used[adj[node][i]] = 1;
                // printf("inquen is %d\n", adj[node][i]);
            }
        // printf("hh is %d tt is %d\n", hh,tt);
    }   
    // printf("counter1 is %d and counter2 is %d\n",counter1,counter2);
    for (i = 0; i <= counter; i++)
    {
        Dnode[dead_stack[i]] = 1;
        // printf("counter is %d\n", counter );
        // printf("dead node is %d\n",dead_stack[i]);
    }
    // exit(1);
    return ;
}

void Dead_node(bool *Dnode){
    int i;
    for (i = 0; i < max_v; ++i)
        if (!Dnode[i] && !isVspec1[i] && !isVspec2[i])
            Bfs_for_D_node(i,Dnode);
}

void zero_adj(){
    int i , j;
    bool tag;
    while(1)
    {
        tag = 0;
        for (i = 0; i < max_v; ++i)
            if(adj[i][0]==0) 
                for (j = 0; j < max_v; ++j)
                    if (g[j][i] < INF)
                    {
                        g[j][i] = INF;
                        g2[j][i] = INF;
                        adj[j][0]--;
                        tag = 1;
                    }
        if(tag == 0)
            return;
    }
}

void Recompute_adj(bool *Dnode){
    int i , j;
    for (i = 0; i < max_v; ++i)
    {
        if(adj[i][0]>0)
        {
            adj[i][0]=0;
            if(!Dnode[i])
                for (j = 0; j < max_v; ++j)
                    if (g[i][j]<INF && !Dnode[j])
                    {
                        adj[i][0]++;
                        adj[i][adj[i][0]]=j;
                    }
         }
    }
}

void Topo_Process(){
    bool Dnode[2008];
    int i , j;
    memset(Dnode,0,sizeof(Dnode));
    Dead_node(Dnode);
    for (i = 0; i < max_v; ++i)
        if (Dnode[i])
            for (j = 0; j < max_v; ++j)
            {
                if(g[i][j] < INF)
                {
                    g[i][j] = INF;
                    g2[i][j] = INF;
                    adj[j][0]--;
                    /* code */
                }
            }
    zero_adj();
    Recompute_adj(Dnode);
}




void CFII_print_path_to_results(long long int res, unsigned short * result1, unsigned short * result2) {

    int edge_id;
    int len;

    if (res < INF) {
        len = path1[0];
        for (int i = 2; i < len; i++) {
            edge_id = data[path1[i - 1]][path1[i]];
            result1[i-2] = edge_id;
            edgesCount[edge_id]++;
        }
        edge_id = data[path1[len - 1]][path1[len]];
        result1[len-2] = edge_id;
        edgesCount[edge_id]++;


        len = path2[0];
        for (int i = 2; i < len; i++) {
            edge_id = data[path2[i - 1]][path2[i]];
            if (edgesCount[edge_id]>0) {
                if (data2[path2[i - 1]][path2[i]]>0)
                    result2[i-2] = data2[path2[i - 1]][path2[i]];
                else
                    result2[i-2] = edge_id;
            }
            else {
                result2[i-2] = edge_id;
            }
        }
        edge_id = data[path2[len - 1]][path2[len]];
        if (edgesCount[edge_id]>0) {
            if (data2[path2[len - 1]][path2[len]]>0)
                result2[len-2] = data2[path2[len - 1]][path2[len]];
            else 
                result2[len-2] = edge_id;
        }
        else {
            result2[len-2] = edge_id;
        }
    }
    else {
        printf("NA error\n");
    }

    return;

}

//你要完成的功能总入口
void search_route(char *topo[MAX_EDGE_NUM], int edge_num, char *demand[MAX_DEMAND_NUM], int demand_num)
{
    unsigned short result1[V_SIZE];//P'路径
    unsigned short result2[V_SIZE];//P''路径

    gettimeofday(&begin_time, NULL);

    /*init global graph info*/
    CFII_read_demands(demand, demand_num);
    CFII_read_topos(topo, edge_num);
    // int counter = 0;
    // int i;
    // for (i = 0; i < max_v; ++i)
    // {
    //     counter += adj[i][0];
    // }
    // // printf("adj before process is %d\n", counter);
    // // Topo_Process();
    // counter = 0;
    // // printf("\nfinish Topo_Process!\n");
    // for (i = 0; i < max_v; ++i)
    // {
    //     counter += adj[i][0];
    // }
    // // printf("adj after process is %d\n", counter);


    AS_T_INIT              = 100;
    AS_FINAL_T             = 0.1;
    AS_COOLING             = 0.99; /* to lower down T (< 1) */

    AS_no_change_time_for_init = 20;
    AS_TRIES_PER_T_for_init    = 100;
    AS_IMPROVED_PATH_PER_T = 15; //50


    AS_no_change_time      = 20;
    AS_TRIES_PER_T         = 10;
    AS_IMPROVED_PATH_PER_T = 5;

    MAX_DFS = 5000;
    cut_low = 0;
    min_cut = 15;
    cut_len = 5;

    if(max_v <= 20) {
        AS_no_change_time = 10;
        AS_TRIES_PER_T = 400;
    }
    // printf("no change time = %d, tries per t = %d, max dfs = %d\n", AS_no_change_time, AS_TRIES_PER_T, MAX_DFS);
    // printf("cut low = %d, min cut = %d, cut len = %d\n\n", cut_low, min_cut, cut_len);

    long long int res;
    find_Craft_solution(max_v, s, t, &res);


    CFII_print_path_to_results(res, result1, result2);
    for (int i = 0; i < path1[0]-1; i++)
    {
        record_result(WORK_PATH, result1[i]);
    }
    for (int i = 0; i < path2[0]-1; i++)
    {
        record_result(BACK_PATH, result2[i]);
    }

    return;
}