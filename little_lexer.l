%{
    /*声明（Declarations）*/
    #include<stdio.h>
    #include<stdlib.h>
    int count=0;//字符数
    int nWord =0;//单词数
    int nRow=0;//行数
%}


/*定义（Definitions）*/
FLOAT [-]?[0-9]+(\.[0-9]+)?
TYPEID Int|Float|String|Bool|Void
KEYWORD fprintf|while|aafor|if|else|continue|break|return
SYMBLE "%"|"~"|"^"|"-"|"*"|"/"|"+"|"-"|";"|":="|"|"|"&"|"{"|"}"|"("|")"|"<"|">"|"%f"|"%s"|"%lld"|"&"|"||"|"&&"
FUNC func(" ")+[a-z][a-zA-Z_0-9]*
OBJECTED [a-z][a-zA-Z_0-9]*
SPECIAL ,|\"


/*规则（Rules）*/
%%

\n {
    nRow++;
    count++;
    }

^{TYPEID}|{KEYWORD}|{FLOAT}|{SYMBLE}|{OBJECTED}|{SPECIAL} {
    nWord++;
    REJECT;
}

[ ]+$ {
    nRow++;
    count++;
    }

 [ ]+ {
    count=count+yyleng;
    nWord++;
}


{SPECIAL} {
    //啥都不做
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

"#" {
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
    nWord++;
    nRow++;
    count++;
}

{FLOAT} {
    printf("\n#%d Const %s",nRow,yytext);
    count=yyleng+count;
}



%%

/*处理函数（User subroutines）*/
int main()
{

    yylex();
    printf("\nlines:%d,words:%d,chars:%d",nRow,nWord,count);
    return(0);
}