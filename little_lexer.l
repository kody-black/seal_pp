%{
    /*声明（Declarations）*/
    #include<stdio.h>
    #include<stdlib.h>
    int count=0;//字符数
    int nWord =0;//单词数
    int nRow=0;
%}


/*定义（Definitions）*/
TYPEID Int|Float|String|Bool|Void
KEYWORD fprintf|while|aafor|if|else|continue|break|return
SYMBLE "%"|"~"|"^"|"-"|"*"|"/"|"+"|"-"|";"|":="|"|"|"&"|"{"|"}"|"("|")"|"|"|"<"|">"|"%f"|"%s"|"%lld"|"|"|"&"|"||"|"&&"
FUNC func(" ")+[a-z][a-zA-Z_0-9]*
OBJECTED [a-z][a-zA-Z_0-9]*


/*规则（Rules）*/
%%

\n {
    nRow+=1;
    }

"stdeer"|"stdout"|,|\" {
    //啥都不做
}


{TYPEID} {
    printf("\n#%d TYPEID %s",nRow,yytext);

}
{KEYWORD} {
    printf("\n#%d KEYWORD %s",nRow,yytext);

}
{OBJECTED} {
    printf("\n#%d OBJECTED %s",nRow,yytext);
}
{SYMBLE} {
    printf("\n#%d %s",nRow,yytext);

}
{FUNC} {
    printf("\n#%d %s",nRow,yytext);
}
"# " {
    char c;
    if(nRow==0)
        printf("#name ");
    while((c=input())!='\n'){
        if(nRow==0)
            putchar(c);
    }
    nRow++;
}

[0-9]+(\.[0-9]+)? {
    printf("\n#%d Const %s",nRow,yytext);
}



%%

/*处理函数（User subroutines）*/
int main()
{

    yylex();
    return(0);
}