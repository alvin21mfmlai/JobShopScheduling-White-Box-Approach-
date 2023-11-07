#include <stdio.h>
#include <stdlib.h>
#include<stdbool.h>

#define N 6 // N jobs, N^2 tasks, machines for each task randomly assigned && PLS CHANGE FOR N BY M PROBLEM
#define M 6 // M machines && PLS CHANGE FOR N BY M PROBLEM
#define MAXMAKESPAN 55 // maximum makespan allowable
#define MAXTIME MAXMAKESPAN // maximum number of grids along time-axis (x-axis) of 2D array
#define MAXMEMO 10000 // 1000000 rows in persistent memo table

#define loop for(;;) // vanilla loop function 
#define jobtaskid(i, j) (i*N + j) // vanilla function to compute task id

// Define data variables //
int data[N][M]; // machine assignment to each jobs; ROW -> job, column -> machine
int time[N][M]; // time required by each machine assigned; ROW -> job, column -> time
int taskNo[N][M]; // task number assigned; ROW -> job, column -> task number
int count = 0; // successful search space count
int count_success = 0; // total successful schedules count
int memoCount = 0; // total memorization subsumption count
int laterCount = 0;
int tabletop = 0; // starting row index for memo table

struct schedulePair{
    int taskID;
    int taskStartingTime;
    int taskEndingTime;
};

struct taskInfo{
    int precedingDone; // 0 represents for preceding task not completed, 1 represents for preceding task completed
    int currentTask; // task ID index
    int currentJob; // job of task ID index
    int taskComplete; // 0 represents not completed task, and vice versa for 1
};

struct machineDict{
    struct taskInfo taskDetail[N*M];
};

typedef struct {
    struct schedulePair schedule[M][N];  // schedule[i][j] = jobtaskid of machine i, j^th task scheduled
    struct machineDict machineInfo[M];   // machineInfo[i][j] = machine i, task ID j
    int frontier[M];                     // frontier[m]: time of last task scheduled on machine m (redundant)
    int nexttask[N];                     // nexttask[j]: for job j, index of next task that can be scheduled (redundant)
    int prevtime[N];                     // prevtime[j]: for job j, the mininum starttime (+1) of the next task in this job (redundant)
    int minStartingTime[N*M];            // minStartingTime[k]: for job k, track its minimum starting time
    int maxStartingTime[N*M];
    int makespan;
    int tasksCompleted;
} sys_state;

struct mainTable{
    sys_state subtable[MAXMEMO];
    int tableTopCounter;
    int memoCounts;
}mainTable[M*N+(1)];

struct taskDuration{
    int duration;
    int jobNumber;
}taskDurationTable[M*N];

struct taskAssoc{
    int prevTask;
    int nextTask;
}taskAssocTable[M*N];

typedef sys_state sys_state;
typedef sys_state interpolant;

// persistent memo table for storing interpolants
// sys_state table[MAXMEMO];

sys_state init();
interpolant solve(sys_state, int);
int subsumed(interpolant);
int equal_schedule(sys_state, sys_state);
int similar_schedule(sys_state, sys_state);
int later_schedule(sys_state, sys_state);
int length(sys_state, int);
int appears(int, sys_state, int);
void output_data();
void output_throughput();
void output_schedule(sys_state);

// Initialization of data structures: (1) assignment of machines to respective task id 
//                                    (2) assignment of processing time for each assigned machine to corresponding task id
                                      
sys_state init() {
    sys_state ss;

    // reading in benchmark text file
    FILE *file;
    int index;
    int *row;
    char ch;
    char *filePath = "6by6.txt"; // PLS CHANGE YOUR FILE PATH //
    FILE *fp = fopen(filePath, "r");

    for (int m = 0; m < M; m++){
        struct machineDict q1;
        for (int x = 0; x < N*M; x++){
            struct taskInfo q2;
            q2.currentTask = -1;
            q2.currentJob = -1;
            q2.precedingDone = 0;
            q2.taskComplete = 0;
            q1.taskDetail[x] = q2;
        }
        ss.machineInfo[m] = q1;
    }

    if (fp == NULL) perror("fopen()");
    int totalTime = 0;
    int maxJobTime = 0;
    for (int j = 0; j < (2*N); j++) {
        if (j < N){
            row  = data[j];
            if (fscanf(fp, "%d%d%d%d%d%d", &row[0], &row[1], &row[2], &row[3], &row[4], &row[5]) == 6){
                for (int k = 0; k < M; k++){
                    if (j < N) {
                        data[j][k] = row[k]; 
                        taskNo[j][k] = jobtaskid(j,k);
                        ss.machineInfo[data[j][k]].taskDetail[taskNo[j][k]].currentJob = j;
                        ss.machineInfo[data[j][k]].taskDetail[taskNo[j][k]].currentTask = taskNo[j][k];
                        ss.machineInfo[data[j][k]].taskDetail[taskNo[j][k]].taskComplete = 0;
                        if (taskNo[j][k] % N == 0) ss.machineInfo[data[j][k]].taskDetail[taskNo[j][k]].precedingDone = 1;
                        else ss.machineInfo[data[j][k]].taskDetail[taskNo[j][k]].precedingDone = 0;
                    }
                }
            }
            ss.nexttask[j] = 0; // initialize next leading task for current job to be zero
            ss.prevtime[j] = -1; // initialize ending time of preceding task to be -1
            ss.makespan = 0; // initialize makespan of schedule to be -1
            ss.tasksCompleted = 0; // initialize number of completed tasks as 0
        }
        else{
            row  = time[j-N];
            int jobTotalTime = 0;
            if (fscanf(fp, "%d%d%d%d%d%d", &row[0], &row[1], &row[2], &row[3], &row[4], &row[5]) == 6){
                for (int k = 0; k < M; k++){
                    taskDurationTable[(j-N)*N + k].duration = row[k];
                    taskDurationTable[(j-N)*N + k].jobNumber = j-N;
                    jobTotalTime += row[k];
                    totalTime += row[k];
                }
            }
            if (jobTotalTime >= maxJobTime) maxJobTime = jobTotalTime;
        }    
    }
    printf("Theoretical Lower Bound = %d\n",maxJobTime);
    printf("Theoretical Upper Bound = %d\n",totalTime);

    for (int m = 0; m < M; m++) {
        printf("Machine No: %d\n", m);
        for (int t = 0; t < N*M; t++) {
            struct schedulePair p1; // initialize schedulePair struct as p1
            p1.taskID = -1; // initialize taskID of p1 as -1
            p1.taskStartingTime = -1; // initialize starting time of p1 as -1
            ss.schedule[m][t-(m*M)] = p1;
            if (ss.machineInfo[m].taskDetail[t].currentTask != -1){
                printf("Current Task: %d, Current Job: %d, Preceding Task Done: %d\n",
                        ss.machineInfo[m].taskDetail[t].currentTask, 
                        ss.machineInfo[m].taskDetail[t].currentJob, 
                        ss.machineInfo[m].taskDetail[t].precedingDone);
            }
        }
        ss.frontier[m] = 0; // initialize frontier timing of all machines as 0
    }
    printf("\n");

    for (int t = 0; t < N*M; t++) {
        mainTable[t].tableTopCounter = 0; // for each quantity of task completed, initialize its visited count as 0
        mainTable[t].memoCounts = 0; // for each quantity of task completed, initialize its total subsumed count as 0
        int currentJobNumber = taskDurationTable[t].jobNumber;
        if (t % N == 0){
            taskAssocTable[t].prevTask = -1;
            taskAssocTable[t].nextTask = t + 1;
        }
        else if ((t+1) % N == 0){
            taskAssocTable[t].prevTask = t - 1;
            taskAssocTable[t].nextTask = -1;
        }
        else{
            taskAssocTable[t].prevTask = t - 1;
            taskAssocTable[t].nextTask = t + 1;
        }
        // printf("Current Task = %d, (Prev = %d, Next = %d)\n", t, taskAssocTable[t].prevTask, taskAssocTable[t].nextTask);
        if (t % N == 0) {
            ss.minStartingTime[t] = 0;
        }
        else{
            ss.minStartingTime[t] = 0;
            for (int x = (currentJobNumber*N); x < t; x++) ss.minStartingTime[t] += taskDurationTable[x].duration;
        }
        ss.maxStartingTime[t] = MAXMAKESPAN-taskDurationTable[t].duration;
        printf("Task #%d: Job Number = %d, Lower Bound = %d, Upper Bound = %d\n",t, currentJobNumber, ss.minStartingTime[t], ss.maxStartingTime[t]);
    }
    return ss;
}

int main() {
    interpolant intp;
    sys_state ss; 
    ss = init(); // initialize partial schedule having 0 tasks assigned
    output_data(); // output data base of tasks, machines and task durations
    intp = solve(ss, 0); // partial schedule, level
    return 0;
}

interpolant solve(sys_state ss, int level) {
    sys_state ss0;
    interpolant intp[N];
	if (count > 10000000) {printf("Abort: count = %d\n", count); exit(0);} // exit once total count exceeeds 10 million quantity
    if (count % 10000 == 0) {printf("Current Search Count = %d, Task Completed = %d\n", count, ss.tasksCompleted);}
    if (subsumed(ss)) return ss;
	mainTable[ss.tasksCompleted].subtable[mainTable[ss.tasksCompleted].tableTopCounter++] = ss;

    intp[0] = ss; 
    if (level >= N*M) {
        count_success++;
        printf(">>>>>>>>>SUCCESS >>>>>>>>>>>> Count/Level %d/%d\n", count, level);
        output_schedule(ss);
        printf("EXIT WITH SUCCESS: total count = %d, equal count = %d, later count = %d, count_success = %d, makespan = %d\n", 
               count, 
               memoCount, 
               laterCount,
               count_success, 
               ss.makespan);
        printf("\n");
        output_throughput();
        exit(0);
        return ss;
    }

    ss0 = ss; // assign current partial schedule state to ss0
    for (int j = 0; j < N; j++) {
        int k = ss.nexttask[j]; // extract index of next task
        if (k == -1) continue; // check if index of next task is -1; if yes, no more tasks to be scheduled for current job

        ss = ss0; // assign ss0 to current partial schedule state
        
        int currentTask = taskNo[j][k]; // extract current task ID to be scheduled
        int job = j; // extract job number for current task ID to be scheduled
        int taskMinStartingTime = ss.minStartingTime[currentTask]; // min. starting time for current task from domain range 
        int m = data[j][k];  // extract machine to manage current task ID
        int f = ss.frontier[m];  // extract  frontier of current machine
        int prev = ss.prevtime[j]; // extract last timing of which the preceding task for current job is completed
        int duration = taskDurationTable[currentTask].duration; // extract duration for current task ID

        // Case 1: last timing of which the preceding task for current job is completed is LESS than the frontier for current machine
        if (prev < f) {
            ss.schedule[m][j].taskStartingTime = ss.frontier[m]; // start of the current task will be the exact frontier of its associated machine
        }
        
        // Case 2: last timing of which the preceding task for current job is completed is GREATER than the frontier for current machine
        else {
            ss.frontier[m] = prev;                               // assign frontier of its associated machine to the last timing of the completed preceding task
            ss.schedule[m][j].taskStartingTime = ss.frontier[m]; // start of the current task will be the exact frontier of its associated machine
        }

        ss.machineInfo[m].taskDetail[currentTask].taskComplete = 1;
        ss.frontier[m] = ss.schedule[m][j].taskStartingTime + duration; // new frontier timing for current machine
        ss.schedule[m][j].taskEndingTime = ss.frontier[m]; // ending time for assigned time -> for convenience

        // CHECK A: if newly computed start time for task exceeds its allowable lower bound //
        if (ss.schedule[m][j].taskStartingTime < taskMinStartingTime) continue;
        if (ss.frontier[m] > ss.makespan) ss.makespan = ss.frontier[m]; 
        // CHECK B: if current makespan of partial schedule exceeds MAXMAKESPAN allowed //
        if (ss.makespan > MAXMAKESPAN) continue; 

        int remainingTaskDuration = 0;
        for (int z = 0; z < N*M; z++){
            if (ss.machineInfo[m].taskDetail[z].currentTask != currentTask){
                // Check if (1) enumerated task within this loop belong to the current machine, and (2) is not assigned yet
                if (ss.machineInfo[m].taskDetail[z].currentTask != -1 && ss.machineInfo[m].taskDetail[z].taskComplete == 0){
                    remainingTaskDuration += taskDurationTable[z].duration;
                    ss.minStartingTime[z] = ss.frontier[m]; // assign current frontier for scheduled t task to lower bound of t'
                }
            }
        }
        // CHECK C: if frontier[m] + sum of remaining tasks to the same machine > MAXMAKESPAN //
        if (ss.frontier[m] + remainingTaskDuration > MAXMAKESPAN) continue; 

        // Passed all previous checks -> proceed to update bounds and mark current task as completed //
        ss.machineInfo[m].taskDetail[currentTask].taskComplete = 1;
        
        // BOUNDS UPDATING: ON SAME JOB //
        int rejectIndicator1 = 0;
        int lowerTaskID = (job*N); int upperTaskID = (job*N)+ (N-1);
        for (int tPrime = 0; tPrime < N*M; tPrime++){
            // SubCase A: Just the next task after the scheduled t task //
            if (tPrime >= lowerTaskID && tPrime <= upperTaskID && tPrime == currentTask+1){
                for (int m_index = 0; m_index < M; m_index++){
                    if (ss.machineInfo[m_index].taskDetail[tPrime].currentTask != -1 && ss.machineInfo[m_index].taskDetail[tPrime].taskComplete == 0){
                        ss.minStartingTime[tPrime] = ss.frontier[m]; // assign current frontier for scheduled t task to lower bound of t'
                        // CHECK D: if updated lower bound of current t' + its own duration exceeds the challenge bound
                        if (ss.minStartingTime[tPrime] + taskDurationTable[tPrime].duration > MAXMAKESPAN) rejectIndicator1 = 1;
                        // CHECK E: if domain is already empty
                        if (ss.maxStartingTime[tPrime] < ss.minStartingTime[tPrime]) rejectIndicator1 = 1;
                    }
                }
            }
            // SubCase B: The susbsequent tasks after the very next task to the scheduled t task //
            else if (tPrime >= lowerTaskID && tPrime <= upperTaskID && tPrime > currentTask+1){
                for (int m_index = 0; m_index < M; m_index++){
                    if (ss.machineInfo[m_index].taskDetail[tPrime].currentTask != -1 && ss.machineInfo[m_index].taskDetail[tPrime].taskComplete == 0){
                        int dummyDuration = 0;
                        for (int z = currentTask+1; z < tPrime; z++){
                            dummyDuration += taskDurationTable[z].duration;
                        }
                        ss.minStartingTime[tPrime] = ss.frontier[m] + dummyDuration;
                        // CHECK F: if updated lower bound of current t' + its own duration exceeds the challenge bound
                        if (ss.minStartingTime[tPrime] + taskDurationTable[tPrime].duration > MAXMAKESPAN) rejectIndicator1 = 1;
                        // CHECK G: if domain is already empty
                        if (ss.maxStartingTime[tPrime] < ss.minStartingTime[tPrime]) rejectIndicator1 = 1;
                    }
                }
            }
        }
        if (rejectIndicator1 == 1) continue;

        // BOUNDS UPDATING: ON SAME MACHINE //
        int rejectIndicator2 = 0;
        int beforeRemainTasksSameMachine [N*M];
        int afterRemainTasksSameMachine [N*M];
        for (int tPrime = 0; tPrime < N*M; tPrime++){
            // Subcase A: t' is not the same job //
            if (tPrime != currentTask && taskDurationTable[tPrime].jobNumber != job){
                // ss.maxStartingTime[tPrime] = ss.frontier[m];
                // CHECK F: if updated lower bound of current t' + its own duration exceeds the challenge bound
                // if (ss.minStartingTime[tPrime] + taskDurationTable[tPrime].duration > MAXMAKESPAN) rejectIndicator2 = 1;
                // CHECK G: if domain is already empty
                // if (ss.maxStartingTime[tPrime] < ss.minStartingTime[tPrime]) rejectIndicator2 = 1;
            }
        }
        if (rejectIndicator2 == 1) continue;

        ss.schedule[m][j].taskID = taskNo[j][k];
        ss.prevtime[j] = ss.frontier[m]; 
        ss.nexttask[j] = ss.nexttask[j] == N-1 ? -1: ss.nexttask[j] + 1; 
        ss.tasksCompleted += 1;

        count++; // increase successful search count by 1
        intp[j] = solve(ss, level+1);
     }
    return ss0;
}

void output_data() {
    for (int j = 0; j < N; j++) {
        printf("Job %d: ", j);
        for (int k = 0; k < M; k++) printf("(m %d, d %d, task %d) ", data[j][k], taskDurationTable[(j*N)+k].duration, taskNo[j][k]);
        printf("\n");
    }
}

void output_schedule(sys_state ss){
    for (int m = 0; m < M; m++){
        printf("Machine %d: ", m);
        for (int t = 0; t < N; t++){
            printf("Task %d = [%d,%d], ", 
            ss.schedule[m][t].taskID, 
            ss.schedule[m][jobtaskid(m,t)-(m*M)].taskStartingTime,
            ss.schedule[m][jobtaskid(m,t)-(m*M)].taskEndingTime);
        }
        printf("\n");
    }
    printf("Span = %d\n", ss.makespan);
}

int subsumed(interpolant ss) {
    int currentCompletedTasksCount = ss.tasksCompleted;
    for (int z = 0; z < MAXMEMO; z++){
        if (equal_schedule(mainTable[currentCompletedTasksCount].subtable[z],ss)) {mainTable[currentCompletedTasksCount].memoCounts+=1; return 1;}
        // if (later_schedule(mainTable[currentCompletedTasksCount].subtable[z],ss)) {mainTable[currentCompletedTasksCount].memoCounts+=1; return 1;}
	    // if (equal_schedule(table[i], ss)) { /*printf("MEMO\n");*/ memoCount+=1; return 1; }
	    // if (later_schedule(table[i], ss)) { /*printf("LATER\n");*/ laterCount+=1; return 1; }
	 }
     return 0;
}

int equal_schedule(sys_state ss1, sys_state ss2) {
    if (ss1.makespan != ss2.makespan) return 0;
    for (int m = 0; m < N; m++) {
        if (ss1.makespan == -1) return 0;
	    for (int t = 0; t < N; t++)
		    if (ss1.schedule[m][jobtaskid(m,t)-(m*M)].taskID != ss2.schedule[m][jobtaskid(m,t)-(m*M)].taskID) return 0;
    }
    return 1;
}

void output_throughput(){
    printf("Tasks Completed    |     Total Visited Counts    |     Total Equal Schedule Memo Counts\n");
    printf("---------------------------------------------------------------------------------------\n");
    for (int t = 0; t <= N*M; t++){
        printf("     %d             |                %d            |              %d\n", t, mainTable[t].tableTopCounter, mainTable[t].memoCounts);
    }
}


// int later_schedule(sys_state ss1, sys_state ss2) {
//     if (ss1.makespan != ss2.makespan) return 0;
//     for (int m = 0; m < N; m++) {
//         if (ss1.makespan == -1) return 0;
// 		int l1 = length(ss1, m); int l2 = length(ss2, m);
// 		if (l1 != l2) return 0;
// 		for (int t = 0; t < N; t++) if (!appears(ss1.schedule[m][jobtaskid(m,t)-(m*M)].taskID, ss2, m)) return 0;

// 	}
//     for (int j = 0; j < N; j++) if (ss1.prevtime[j] > ss2.prevtime[j]) return 0;
//     return 1;
// }

// int length(sys_state ss, int m) {
//     int z = 0;
//     for (int t = 0; t < N; t++) if (ss.schedule[m][jobtaskid(m,t)-(m*M)].taskEndingTime != -1) z++;
//     return z;
// }

// int appears(int taskid, sys_state ss, int m) {
//      for (int t = 0; t < N; t++) if (ss.schedule[m][jobtaskid(m,t)-(m*M)].taskID == taskid) return 1;
//      return 0;
// }

// int similar_schedule(sys_state ss1, sys_state ss2) {
//     if (ss1.makespan != ss2.makespan) return 0;
//     for (int m = 0; m < N; m++) {
//         if (ss1.makespan == -1) return 0;
// 		int l1 = length(ss1, m); int l2 = length(ss2, m);
// 		if (l1 != l2) return 0;
// 		for (int t = 0; t < N*M; t++) if (!appears(ss1.schedule[m][t].taskID, ss2, m)) return 0;
// 	}
//     return 1;
// }
