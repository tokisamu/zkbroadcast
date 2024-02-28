#include "../src/params.h"
#include "../src/sigmaplus_prover.h"
#include "../src/sigmaplus_verifier.h"
#include "../src/message.h"
#include "../src/message.hpp"
#include<iostream>
#include<fstream>
#include <stdlib.h>
#include<memory.h>
#include<algorithm>
#include<map>
#include<set>
struct task
{
    int user;
    int message_id;
    int valid_time;
};
void remove(std::vector<int> &v)
{
    auto end = v.end();
    for (auto it = v.begin(); it != end; ++it) {
        end = std::remove(it + 1, end, *it);
    }
 
    v.erase(end, v.end());
}
int main()
{
    ifstream ifs;
    int number_nodes = 1000;
    int degree_random = 6;
    int nums_friend = 20;
    //people mobility dataset
    //data form: 2013-02-06T07:00:05:196;PIW;78230;20890;1
    ifs.open("al_position2013-02-06.csv",ios::in);
    char buf[1000] = {0};
    int nodeid = -1;
    int nodecnt = -1;
    int duration = 999999;
    int maxd = 0;
    int messagecnt[100000];
    int starttime[100000];
    int endtime[100000];
    vector<vector<int>> temphop0friend;
    vector<vector<int>> temphop1friend;
    std::set<pair<int,int>> hop0friend;
    std::set<pair<int,int>> hop1friend;
    std::set<pair<int,int>> hop2friend;
    
    //construct friendship relation
    
    for(int i=0;i<number_nodes;i++)
    {
        vector<int> temp;
        temphop0friend.push_back(temp);
        vector<int> temp2;
        temphop1friend.push_back(temp2);
    }
    for(int i=0;i<number_nodes;i++)
    {
        for(int j=0;j<nums_friend;j++)
        {
            int next = rand()%number_nodes;
            if(next==i) next = (next+1)%number_nodes;
            while(hop0friend.count(make_pair(i,next)))
            {
                next = rand()%number_nodes;
                if(next==i) next = (next+1)%number_nodes;
            }
            hop0friend.insert(make_pair(i,next));
            hop0friend.insert(make_pair(next,i));
            temphop0friend[i].push_back(next);
            temphop0friend[next].push_back(i);
        }
    }
    for(int i=0;i<number_nodes;i++)
    {
        int cnt2 = 0;
        for(int j=0;j<number_nodes;j++)
        {
            int cnt = 0;
            for(int k=0;k<temphop0friend[i].size();k++)
            {
                if(hop0friend.count(make_pair(j,temphop0friend[i][k]))>0)
                {
                    cnt++;
                }
            }
            if((double)cnt/temphop0friend[i].size()>0.1)
            {
                cnt2++;
                hop1friend.insert(make_pair(i,j));
                temphop1friend[i].push_back(j);
            }
        }
        cout<<cnt2<<endl;
    }
    for(int i=0;i<number_nodes;i++)
    {
        int cnt = 0;
        for(int j=0;j<temphop1friend[i].size();j++)
        {
            for(int k=0;k<temphop1friend[temphop1friend[i][j]].size();k++)
            {
                if(hop2friend.count(make_pair(i,temphop1friend[temphop1friend[i][j]][k]))==0)
                {
                    cnt++;
                    hop2friend.insert(make_pair(i,temphop1friend[temphop1friend[i][j]][k]));
                    hop2friend.insert(make_pair(temphop1friend[temphop1friend[i][j]][k],i));
                }
            }
        }
        cout<<i<<" has "<<cnt<<" friends"<<endl;
    }
    cout<<"use trust network"<<endl;
    for(int i=0;i<number_nodes;i++)
    {
        temphop0friend[i].clear();
        temphop1friend[i].clear();
    }
    temphop0friend.clear();
    temphop1friend.clear();
    hop0friend.clear();
    
    memset(messagecnt,0,sizeof(messagecnt));
    memset(starttime,0,sizeof(starttime));
    memset(endtime,0,sizeof(endtime));
    vector<vector<int>> positionx;
    vector<vector<int>> positiony;
    while(ifs>>buf)
    {
        //cout<<buf<<endl;
        const char *d = ";";
        char *p;
        int cnt = 0;
        p = strtok(buf,d);
        int x,y;
        while(p)
        {
            cnt++;
            //cout<<p<<endl;
            if(cnt==3)
            {
                x = atoi(p);
            }
            else if(cnt==4)
            {
                y = atoi(p);
            }
            else if(cnt==5)
            {
                int temp = atoi(p)-1;
                if(temp!=nodeid)
                {
                    //cout<<nodecnt<<" "<<x<<" "<<y<<endl;
                    nodeid = temp;
                    if(nodecnt>0&&positionx[nodecnt].size()<1000)
                    {
                        positionx[nodecnt].clear();
                        positiony[nodecnt].clear();
                        positionx[nodecnt].push_back(x);
                        positiony[nodecnt].push_back(y);
                    }
                    else
                    {
                        nodecnt++;
                        vector<int> newnodex;
                        vector<int> newnodey;
                        positionx.push_back(newnodex);
                        positionx[nodecnt].push_back(x);
                        positiony.push_back(newnodey);
                        positiony[nodecnt].push_back(y);
                        if(nodecnt>1)
                        {
                            int lastduration = positionx[nodecnt-1].size();
                            duration = min(duration,lastduration);
                            maxd = max(maxd,lastduration);
                        }
                    }
                }
                else
                {
                    positionx[nodecnt].push_back(x);
                    positiony[nodecnt].push_back(y);
                }
            }
            p = strtok(NULL,d);
        }
    }
    int node_queue[number_nodes][number_nodes];
    int node_cnt[number_nodes];
    std::set<pair<int,int>> deleted;
    std::set<pair<int,int>> message_map1;
    std::set<pair<int,int>> message_map2;
    for(int i=0;i<number_nodes;i++)
        node_cnt[i] = 0;
    std::cout<<"???"<<" "<<duration<<" "<<maxd<<endl;
    vector<sigma::SigmaPlusProof<secp_primitives::Scalar,secp_primitives::GroupElement>>  proofs;
    vector<vector<task>> task_queue;
    vector<vector<int>> topology;
    std::vector<secp_primitives::Scalar> secrets;
    std::vector<sigma::SigmaPlusProver<secp_primitives::Scalar,secp_primitives::GroupElement>> provers;
    std::vector<sigma::Message<secp_primitives::Scalar,secp_primitives::GroupElement>> messages;
    std::vector<secp_primitives::GroupElement> commits;
    for(int i=0;i<600;i++)
    {
        vector<task> temp;
        task_queue.push_back(temp);
    }
    for(int i=0;i<number_nodes;i++)
    {
        vector<int> temp;
        topology.push_back(temp);
    }
    //complete graph at first
    
    int sum_degree=0;
    for(int i=0;i<10;i++)
    {
        for(int j=i;j<10;j++)
        {
            topology[i].push_back(j);
            topology[j].push_back(i);
            sum_degree+=2;
        }
    }
    
    //add new node
    
    for(int i=10;i<number_nodes;i++)
    {
        int flag = 0;
        while(flag==0)
        for(int j=0;j<i;j++)
        {
            if(rand() % 100<((double)topology[j].size()/double(sum_degree))*100.0*degree_random)
            {
                flag = 1;
                topology[j].push_back(i);
                topology[i].push_back(j);
                sum_degree+=2;
            }
        }
    }

    auto params = sigma::Params::get_default();
    int N = 16384;
    int time_slots=10;
    int n = params->get_n();
    int m = params->get_m();
    std::vector<int> indexs;
    int index = 0;
    secp_primitives::GroupElement g;
    g.randomize();
    std::vector<secp_primitives::GroupElement> h_gens;
    h_gens.resize(n * m);
    for(int i = 0; i < n * m; ++i ){
        h_gens[i].randomize();
    }
    //initialize users' commits
    
    for(int i = 0; i < N/time_slots-1; ++i){
        indexs.push_back(rand() % time_slots);
        for(int j=0;j<time_slots;j++)
        {
            if(j==indexs[i])
            {
                secp_primitives::Scalar r;
                r.randomize();
                secrets.push_back(r);
                sigma::SigmaPlusProver<secp_primitives::Scalar,secp_primitives::GroupElement> prover(g,h_gens, n, m);
                provers.push_back(prover);
                secp_primitives::GroupElement c;
                secp_primitives::Scalar zero(unsigned(0));
                c = sigma::SigmaPrimitives<secp_primitives::Scalar,secp_primitives::GroupElement>::commit(g, zero, h_gens[0], r);
                commits.push_back(c);
            }
            else
            {
                commits.push_back(secp_primitives::GroupElement());
                commits[i*time_slots+j].randomize();
            }
        }
    }
    //sigma::SigmaPlusVerifier<secp_primitives::Scalar,secp_primitives::GroupElement> verifier(g, h_gens, n, m);
    int cycle = 1;
    int message_cnt = 0;
    int attack_cnt = 0;
    while(cycle--)
    {
        for(int i=0;i<600;i++)
            task_queue[i].clear();
        memset(node_cnt,0,sizeof(node_cnt));
        message_map1.clear();
        message_map2.clear();
        message_cnt = 0;
        attack_cnt = 0;
        deleted.clear();
        for(int i=0;i<number_nodes;i++)
        {
            for(int j=0;j<number_nodes;j++)
                node_queue[i][j] = 0;
        }
        for(int t=0;t<300;t++)
        {
            int ddd = 0;
            
            //create dynamic  topology
            for(int j=0;j<number_nodes;j++)
            {
                topology[j].clear();
                //cout<<"hhhh: "<<j<<" "<<topology[j].size()<<endl;
            }
            for(int j=0;j<number_nodes;j++)
            {
                //cout<<"xxxx: "<<j<<endl;
                int deg=0;
                for(int k=0;k<number_nodes;k++)
                {
                    //cout<<"kkk: "<<k<<endl;
                    if(j==k) continue;
                    if((positionx[j][t*2]-positionx[k][t*2])*(positionx[j][t*2]-positionx[k][t*2])+(positiony[j][t*2]-positiony[k][t*2])*(positiony[j][t*2]-positiony[k][t*2])<200
                        ||(positionx[j][t*2+1]-positionx[k][t*2+1])*(positionx[j][t*2+1]-positionx[k][t*2+1])+(positiony[j][t*2+1]-positiony[k][t*2+1])*(positiony[j][t*2+1]-positiony[k][t*2+1])<200)
                    {
                        deg++;
                    }
                }
                if(deg>0)
                for(int k=0;k<number_nodes;k++)
                {
                    //cout<<"ggg: "<<k<<endl;
                    if(j==k) continue;
                    if(((positionx[j][t*2]-positionx[k][t*2])*(positionx[j][t*2]-positionx[k][t*2])+(positiony[j][t*2]-positiony[k][t*2])*(positiony[j][t*2]-positiony[k][t*2])<200
                        ||(positionx[j][t*2+1]-positionx[k][t*2+1])*(positionx[j][t*2+1]-positionx[k][t*2+1])+(positiony[j][t*2+1]-positiony[k][t*2+1])*(positiony[j][t*2+1]-positiony[k][t*2+1])<200
                        )&&rand()%deg<10)
                    {
                        int flag = 0;
                        for(int l=0;l<topology[j].size();l++)
                        {
                            if(topology[j][l]==k){
                                flag = 1;
break;
                                }
                        }
                        if(flag) continue;
                        topology[j].push_back(k);
                        topology[k].push_back(j);
                        ddd+=2;
                    }
                }
                else
                {
                    int temp = rand()%number_nodes;
                    topology[j].push_back(temp);
                    topology[temp].push_back(j);
                    ddd+=2;
                }
            }
            
            if(t%20==0)
            {
                if((t/20)%2==0)
                {
                    message_map1.clear();
                }
                else
                {
                    message_map2.clear();
                }
            }
            if(t%10==0&&t>50)
            {
                for(int i=0;i<10;i++)
                {
                    task_queue[t-50+i].clear();
                }
                //cout<<"deleted"<<endl;

 
            }
            if(t%20==0)
                std::cout<<"time: "<<t<<" "<<ddd<<std::endl;
            for(int user=0;user<number_nodes;user++)
            {
                if(user%100==13)
                {
                    for(int i=0;i<50;i++)
                    {
                        task t1;
                        attack_cnt++;
                        t1.message_id = attack_cnt-1+10000000;
                        t1.user = user;
                        t1.valid_time = t+30;
                        task_queue[t].push_back(t1);
                        if((t/20)%2==0)
                            message_map1.insert(make_pair(t1.message_id,user));
                        else
                            message_map2.insert(make_pair(t1.message_id,user));
                        node_queue[user][node_cnt[user]]=t1.message_id;
                        node_cnt[user]=(node_cnt[user]+1)%100;
                    }
                }
                else if(rand()%100>98)
                {
                    std::string s = "msg"+ std::to_string(message_cnt);
                    char *mm = &s[0];
                    index = user*time_slots;
                    //sigma::SigmaPlusProof<secp_primitives::Scalar,secp_primitives::GroupElement> prf(n,m);
                    //provers[user].proof(commits, index+indexs[user], secrets[user], true, prf,mm);
                    //proofs.push_back(prf);
                    //sigma::SigmaPlusProof<secp_primitives::Scalar,secp_primitives::GroupElement> *pproof = &prf;
                    //sigma::Message<secp_primitives::Scalar,secp_primitives::GroupElement> meme(message_cnt++,mm,t,pproof);
                    //messages.push_back(meme);
                    task t1;
                    message_cnt++;
                    t1.message_id = message_cnt-1;
                    t1.user = user;
                    t1.valid_time = t+30;
                    task_queue[t].push_back(t1);
                    messagecnt[t1.message_id]++;
                    starttime[t1.message_id] = t;
                    if((t/20)%2==0)
                        message_map1.insert(make_pair(t1.message_id,user));
                    else
                        message_map2.insert(make_pair(t1.message_id,user));
                    node_queue[user][node_cnt[user]]=t1.message_id;
                    node_cnt[user]=(node_cnt[user]+1)%100;
                    //std::cout<<"new message: "<<user<<" "<<indexs[user]<<" "<<mm<<std::endl;
                }
            }
            for(int tt=0;tt<task_queue[t].size();tt++)
            {
                task t1 = task_queue[t][tt];
                std::string s = "msg"+ std::to_string(t1.message_id);
                char *mm = &s[0];
                int user = t1.user;
                auto iter = deleted.count(make_pair(t1.message_id,user));
                if(iter > 0)
                    continue;
                //std::cout<<std::endl;
                //std::cout<<t1.message_id<<" "<<user<<" "<<" next: ";
                for(int i=0;i<topology[user].size();i++)
                //for(int i=0;i<neighbor[user][t/5].size();i++)
                {
                    int next = topology[user][i];
                    //trust network
                    if(hop2friend.count(make_pair(user,next))==0)
                        continue;
                    //std::cout<<next<<" ";
                    //int next = neighbor[user][t/5][i];
                    auto iter2 = message_map1.count(make_pair(t1.message_id,next))+message_map2.count(make_pair(t1.message_id,next));
                    if(iter2 == 0)
                    {
                        //std::cout<<"message next: "<<next<<std::endl;
                        if(t1.message_id<10000000)
                            messagecnt[t1.message_id]++;
                        if((t/20)%2==0)
                            message_map1.insert(make_pair(t1.message_id,next));
                        else
                            message_map2.insert(make_pair(t1.message_id,next));
                        task t2;
                        t2.message_id = t1.message_id;
                        t2.user = next;
                        if(node_queue[next][node_cnt[next]]!=0)
                        {
                            deleted.insert(make_pair(node_queue[next][node_cnt[next]],next));
                            //std::cout<<"message deleted: "<<next<<" "<<t1.message_id<<std::endl;
                        }
                        node_queue[next][node_cnt[next]]=t1.message_id;
                        node_cnt[next]=(node_cnt[next]+1)%100;
                        int nexttime = t+rand()%3;
                        if(t2.message_id<100000)
                            endtime[t2.message_id] = max(endtime[t2.message_id],nexttime);
                        task_queue[nexttime].push_back(t2);
                        //if(t>t1.valid_time)
                        //    break;
                    }
                }
            }
            if(t%100==49)
                for(int i=0;i<message_cnt;i++)
                {
                    std::cout<<"message broadcast count: "<<i<<" "<<messagecnt[i]<<std::endl;
                }
        }
        int success = 0;
        int totaldelay = 0;
        int totalbroadcast = 0;
        for(int i=0;i<message_cnt;i++)
        {
            totalbroadcast+=messagecnt[i];
            cout<<messagecnt[i]<<endl;
            std::cout<<"message broadcast count: "<<i<<" "<<messagecnt[i]<<std::endl;
            if(messagecnt[i]>950)
            {
                success++;
                totaldelay+=(endtime[i]-starttime[i]);
            }
        }
        cout<<"success rate: "<<(double)success/message_cnt<<endl;
        cout<<"delay: "<<double(totaldelay)/success<<endl;
        cout<<"coverage rate: "<<double(totalbroadcast)/double(message_cnt*number_nodes)<<endl;
    }
    /*
    real test
    while(cycle--)
    {
        for(int t=0;t<600;t++)
        {
            for(int user=0;user<100;user++)
            {
                if(indexs[user]==t/60&&vis[user]==0)
                {
                    std::string s = "msg"+ std::to_string(message_cnt);
                    char *mm = &s[0];
                    vis[user] = 1;
                    index = user*time_slots;
                    sigma::SigmaPlusProof<secp_primitives::Scalar,secp_primitives::GroupElement> prf(n,m);
                    provers[user].proof(commits, index+indexs[user], secrets[user], true, prf,mm);
                    proofs.push_back(prf);
                    sigma::SigmaPlusProof<secp_primitives::Scalar,secp_primitives::GroupElement> *pproof = &prf;
                    sigma::Message<secp_primitives::Scalar,secp_primitives::GroupElement> meme(message_cnt++,mm,t,pproof);
                    messages.push_back(meme);
                    task t1;
                    t1.message_id = message_cnt-1;
                    t1.user = user;
                    task_queue[t].push_back(t1);
                    vector<int> temp;
                    message_node_map.push_back(temp);
                    message_node_map[t1.message_id].push_back(t1.user);
                    std::cout<<"new message: "<<user<<" "<<indexs[user]<<" "<<verifier.verify(commits, *(meme.proof), true,mm)<<" "<<mm<<std::endl;
                }
            }
            for(int tt=0;tt<task_queue[t].size();tt++)
            {
                task t1 = task_queue[t][tt];
                std::string s = "msg"+ std::to_string(t1.message_id);
                char *mm = &s[0];
                int user = t1.user;
                std::cout<<"handle message: "<<t<<" "<<t1.user<<" "<<t1.message_id<<" "<<mm<<std::endl;
                if(!verifier.verify(commits, proofs[t1.message_id], true,mm))
                {
                    std::cout<<"failed "<<std::endl;
                    continue;
                }
                for(int i=0;i<topology[user].size();i++)
                {
                    int next = topology[user][i];
                    int flag = 1;
                    for(int j=0;j<message_node_map[t1.message_id].size();j++)
                    {
                        if(message_node_map[t1.message_id][j]==next)
                        {
                            flag = 0;
                            break;
                        }
                    }
                    if(flag)
                    {
                        message_node_map[t1.message_id].push_back(next);
                        task t2;
                        t2.message_id = t1.message_id;
                        t2.user = next;
                        task_queue[t+1].push_back(t2);
                    }
                }
            }
        }
    }
    */
}