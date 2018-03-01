#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>

using namespace std;

#define x first
#define y second
#define pb push_back
#define cout fout

int Reg[32], Mem[32], RegUse[32];
string instruction[5] = {"lw", "sw", "add", "sub", "beq"};
string stage[6] = {"IF", "ID", "EX", "MEM", "WB", ""};
string singal[5][3] = {{"01", "010", "11"},  // lw
                       {"X1", "001", "0X"},  // sw
                       {"10", "000", "10"},  // r-format
                       {"10", "000", "10"},  // r-format
                       {"X0", "100", "0X"}}; // beq
struct INSTR
{
    int instr, rd, rt, rs;
    INSTR(int in, int d, int t, int s)
        : instr(in), rd(d), rt(t), rs(s){}
};
vector<string> input;       // 儲存輸入的每一行指令(字串)
vector<INSTR> cases;        // 儲存解析後的指令
vector<int> *pipeline;      // 儲存pipeline stage的每個狀態

void init()
{
    for(int i=0; i<32; i++)
        Reg[i] = Mem[i] = 1;
    Reg[0] = 0;
    for(int i=0; i<32; i++)
        RegUse[i] = 0;
    input.clear();
    cases.clear();
}

// 偵測指令的編號
int IF(string str)
{
    for(int i=0; i<5; ++i)
        if(str == instruction[i])
            return i;
    return -1;
}

// 將指令展開後推進cases(vector)中, 同時計算Reg & Mem結果
// 回傳pc下一個位置
int build(string str, int pc)
{
    // 把指令中除了數字以外的符號轉成空白, 以利stringstream切割
    size_t i = 0;
    string token = ",$()\n\r\t";
    while(string::npos != (i = str.find_first_of(token,i)))
        str.replace(i, 1, " ");
    stringstream ss(str);
    ss >> str;
    int instr = IF(str), rd, rt, rs, offset, base, L1;

    // 若會被beq跳過的指令照樣推進cases, 但不做Reg & Mem運算
    if(pc == -1)
    {
        ss >> rd >> rt >> rs;
        rd = rt = rs = -1;
        cases.push_back(INSTR(instr, rd, rt, rs));
        return -1;
    }

    // 在解析指令的同時計算結果
    switch(instr)
    {
        case 0: //lw
            ss >> rt >> offset >> base;
            cases.push_back(INSTR(instr, rt, offset, base));
            Reg[rt] = Mem[(base+offset) / 4];
            break;
        case 1: //sw
            ss >> rt >> offset >> base;
            cases.push_back(INSTR(instr, rt, offset, base));
            Mem[(base+offset) / 4] = Reg[rt];
            break;
        case 2: //add
            ss >> rd >> rs >> rt;
            cases.push_back(INSTR(instr, rd, rs, rt));
            Reg[rd] = Reg[rs] + Reg[rt];
            break;
        case 3: //sub
            ss >> rd >> rs >> rt;
            cases.push_back(INSTR(instr, rd, rs, rt));
            Reg[rd] = Reg[rs] - Reg[rt];
            break;
        case 4: //beq
            ss >> rs >> rt >> L1;
            cases.push_back(INSTR(instr, rs, rt, L1));
            if(Reg[rs] == Reg[rt])
                pc += L1;
            break;
    }

    return pc;
}

int IsHazard(int idx)
{
    // 上一個指令是beq則要先等候
    if(cases[idx-1].instr == 4)
        return 1;

    switch(cases[idx].instr)
    {
        case 0: // lw
        case 1: // sw
        case 2: // add
        case 3: // sub
            if(RegUse[cases[idx].rs] || RegUse[cases[idx].rt])
                return 2;
        case 4: //beq
            if(RegUse[cases[idx].rd] || RegUse[cases[idx].rt])
                return 2;
        default:
            return 0;
    }

    return 0;
}

// 進行指令管線化, n為所有指令數量, 用idx逐個進行排程
void pipeline_stage(int n)
{
    int idx = 0;
    while(idx < n)
    {
        //cout << instruction[ cases[idx].instr ] << " " << cases[idx].rd << " " << cases[idx].rt << " " << cases[idx].rs << endl;

        // 將now指到第一個非階段5(空白)的位置
        int now = -1;
        while(pipeline[idx][++now] == 5);

        // 調整階段1(IF)的位置
        for(int i=now; i<pipeline[idx-1].size() && idx>0; i++)
        {
            // 若前一指令同個位置還是階段5(空白), 則整個指令向後移(補5空白)
            if(pipeline[idx-1][i] == 5)
                pipeline[idx].insert(pipeline[idx].begin()+i, pipeline[idx][i-1]);
            // 若前一指令同個位置階段相同, 則整個指令向後移(補前一個階段)
            else if(pipeline[idx][i] == pipeline[idx-1][i])
                pipeline[idx].insert(pipeline[idx].begin()+i, pipeline[idx][i-1]);
        }

        // 發生data hazard
        if(IsHazard(idx) == 2)
        {
            // 將now移動到階段1(ID)出現的位址
            while(pipeline[idx][now] != 1)
                now++;
            // insert bubble
            for(int i=now; i<pipeline[idx-1].size()-1; i++)
                pipeline[idx].insert(pipeline[idx].begin()+i, pipeline[idx][i]);
        }
        // beq的下個指令須先暫停
        else if(IsHazard(idx)==1 && idx>0)
        {
            // 將now移動到階段1(ID)出現的位址
            while(pipeline[idx][now] != 1)
                now++;
            // 若beq下個指令不會執行(rd=rt=rs=-1) 則把階段1,2,3,4刪除
            if(cases[idx].rd==cases[idx].rt && cases[idx].rt==cases[idx].rs && cases[idx].rs==-1)
                pipeline[idx].erase (pipeline[idx].begin()+now, pipeline[idx].end());
            // 反之若下個指令會執行 則多空一個階段0(IF)
            else
                pipeline[idx].insert(pipeline[idx].begin()+now, pipeline[idx][now-1]);
            // 等待beq也算執行一次指令, 因此要將rd的使用減1
            for(int i=0; i<32; i++)
                if(RegUse[i] != 0)
                    RegUse[i]--;
        }

        // 有用到rd的的指令使用時加2, 之後每跑一個指令將減1, 直到0為止
        if(cases[idx].rd != -1) //防beq的下個指令為-1
            RegUse[cases[idx].rd] += 2;
        for(int i=0; i<32; i++)
            if(RegUse[i] > 0)
                RegUse[i]--;
/*
        for(int i=0; i<pipeline[idx].size(); i++)
            cout << pipeline[idx][i] << " ";
        cout << endl;
*/
        idx++;
    }
}

int main()
{
    string str;
    ifstream fin;
    ofstream fout;
    fin.open("memory.txt", ios::in);
    fout.open("result.txt", ios::out);
    while(!fin.eof())
    {
        init();
        // 將檔案的每一行字串推進input(vector)
        while(getline(fin, str) && str!="")
            input.push_back(str);
        // 把每一行指令展開後建成cases(vector), 注意beq下個指令的去向
        for(int i=0, next=0; i<input.size(); )
        {
            next = build(input[i], i+1);
            if(next == i+1)
                i++;
            // 若會被beq跳過,先將原本要做的下句存起來,再jump
            else
            {
                build(input[i+1], -1);
                i = next;
            }
        }

        // 事先把pipeline的表格建好, 之後用pipeline_stage進行調整
        int n = cases.size();
        pipeline = new vector<int>[n];
        for(int i=0; i<n; i++)
        {
            pipeline[i].clear();
            for(int j=0; j<i; j++)
                pipeline[i].pb(5);
            for(int j=i,idx=0; j<i+5; j++)
                pipeline[i].pb(idx++);
        }
/*
        for(int i=0; i<cases.size(); i++)
            cout << instruction[ cases[i].instr ] << " " << cases[i].rd << " " << cases[i].rt << " " << cases[i].rs << endl;
*/
        pipeline_stage(n);

        // 計算最長cycle, 並把每一指令的空白部分填滿
        int cycle = pipeline[n-1].size();
        for(int i=0; i<n; i++)
            while(pipeline[i].size() < cycle)
                pipeline[i].pb(5);

        // debug
        string _stage[6] = {" IF", " ID", " EX", "MEM", " WB", "   "};
        for(int i=0; i<n; i++)
        {
            for(int j=0; j<pipeline[i].size(); j++)
                cout << _stage[ pipeline[i][j] ] << " ";
            cout << endl;
        }

        // result
        for(int i=0; i<cycle; i++)
        {
            cout << "Cycle " << i+1 << ":\n";
            for(int j=0; j<n; j++)
                if(pipeline[j][i] != 5)
                {
                    cout << "  " << instruction[ cases[j].instr ] << ": " << stage[ pipeline[j][i] ];
                    for(int k=pipeline[j][i]-2; k<3 && k>=0; k++)
                        cout << " " << singal[cases[j].instr][k];
                    cout << endl;
                }
        }
        cout << ">>> " << cycle << " cycles" << endl;
        cout << "Reg: ";
        for(int i=0; i<32; i++)
        {
            cout << Reg[i];
            if(i%8 == 7)
                cout << " ";
        }
        cout << "\nMem: ";
        for(int i=0; i<32; i++)
        {
            cout << Mem[i];
            if(i%8 == 7)
                cout << " ";
        }
        cout << endl << endl;

        cin.get();
    }
    fin.close();
    fout.close();
    return 0;
}
