%{
    /*声明（Declarations）*/
    #include<stdio.h>
    #include<stdlib.h>
    int count=0;//字符数
    int nWord =0;//单词数
    int nRow=0;//行数
%}


/*定义（Definitions）*/
NUM [0-9]+(\.[0-9]+)?
/*NUM [-]?[0-9]+(\.[0-9]+)?*/
TYPEID Int|Float|String|Bool|Void
KEYWORD fprintf|while|aafor|if|else|continue|break|return
SYMBLE "%"|"~"|"^"|"-"|"*"|"/"|"+"|"-"|";"|":="|"|"|"&"|"{"|"}"|"("|")"|"<"|">"|"<="|">="|"=="|"%f"|"<="|">="|"=="|"%s"|"%lld"|"&"|"||"|"&&"
FUNC func(" ")+[a-z][a-zA-Z_0-9]*
OBJECTED [a-z][a-zA-Z_0-9]*
SPECIAL ,|\"


/*规则（Rules）*/
%%

\n {
    nRow++;
    count++;
    }

^{TYPEID}|{KEYWORD}|{NUM}|{SYMBLE}|{OBJECTED}|{SPECIAL}|# {
    //防止匹配到的内容放在首部，前面无空格，出现单词数目不增加的情况
    nWord++;
    REJECT;
}

[ ]+$ {
    //处理掉句末和#前的空格
    
    nRow++;
    count=count+yyleng;
    }

 [ ]+ {
     //出现空格，而且后面有内容，则字数加1
    count=count+yyleng;
       nWord++;
}


{SPECIAL} {
    //，和“直接忽略，啥都不做
    count=yyleng+count;
}

{TYPEID} {
    printf("\n#%d TYPEID %s",nRow,yytext);
    count=yyleng+count;
}

{KEYWORD} {
    printf("\n#%d KEYWORD %s",nRow,yytext);
    count=yyleng+count;
}

{OBJECTED} {
    if((yytext!="stdeer")&&(yytext!="stdout"))
        printf("\n#%d OBJECTED %s",nRow,yytext);
    count=yyleng+count;
}

{SYMBLE} {
    if(yytext!=",")
        printf("\n#%d %s",nRow,yytext);
    count=yyleng+count;
}

{FUNC} {
    printf("\n#%d %s",nRow,yytext);
       nWord++;
    count=yyleng+count;
}


{NUM} {
    printf("\n#%d Const %s",nRow,yytext);
    count=yyleng+count;
}


"#" {
    //处理注释情况，默认第一行注释则认为是标题进行显示，其他注释直接不显示
    //注释中的字符数和单词数同样统计
    
    char c;
    count++;
    if(nRow==0)
        printf("#name");
        
    c=input();
    while(c!='\n'){
        if(nRow==0)
            putchar(c);
        if(c==' ')
        {
            while((c=input())==' ')
            {
                if(nRow==0)
                    putchar(c);
                count++;
            }
            if(c!='\n')
            {
                   nWord++;
                count++;
            }
        }
        else
        {
            count++;
            c=input();
        }
    }
    nRow++;
    count++;
}



%%

/*处理函数（User subroutines）*/
int main()
{

    yylex();
    printf("\nlines:%d,words:%d,chars:%d",nRow,nWord,count);
    return(0);
}