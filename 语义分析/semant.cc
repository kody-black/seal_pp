#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"
#include <map>

using namespace std;
extern int semant_debug;
extern char *curr_filename;

static ostream& error_stream = cerr;
static int semant_errors = 0;
static Decl curr_decl = 0;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name, type
ObjectEnvironment objectEnv;
typedef std::map<Symbol, Decl_class*> variabletable; 
variabletable variableTable;
typedef std::map<Symbol, Decl_class*> funcTable;  
funcTable FuncTable;

///////////////////////////////////////////////
// helper func
///////////////////////////////////////////////


static ostream& semant_error() {
    semant_errors++;
    return error_stream;
}

static ostream& semant_error(tree_node *t) {
    error_stream << t->get_line_number() << ": ";
    return semant_error();
}

static ostream& internal_error(int lineno) {
    error_stream << "FATAL:" << lineno << ": ";
    return error_stream;
}

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////

static Symbol 
    Int,
    Float,
    String,
    Bool,
    Void,
    Main,
    print
    ;

bool isValidCallName(Symbol type) {
    return type != (Symbol)print;
}

bool isValidTypeName(Symbol type) {
    return type != Void;
}

//
// Initializing the predefined symbols.
//

static void initialize_constants(void) {
    // 4 basic types and Void type
    Bool        = idtable.add_string("Bool");
    Int         = idtable.add_string("Int");
    String      = idtable.add_string("String");
    Float       = idtable.add_string("Float");
    Void        = idtable.add_string("Void");  
    // Main function
    Main        = idtable.add_string("main");

    // classical function to print things, so defined here for call.
    print        = idtable.add_string("printf");
}

/*
    TODO :
    you should fill the following function defines, so that semant() can realize a semantic 
    analysis in a recursive way. 
    Of course, you can add any other functions to help.
*/

static bool sameType(Symbol name1, Symbol name2) {
    return strcmp(name1->get_string(), name2->get_string()) == 0;
}

static void install_calls(Decls decls) {
    for (int i = decls->first(); decls->more(i); i = decls->next(i))
    {
        Decl curr_callDecl = decls->nth(i);
        Symbol name = curr_callDecl->getName();
        if(curr_callDecl->isCallDecl()){
            if (FuncTable.find(name) != FuncTable.end()) {
                semant_error(curr_callDecl)<<"Function "<<curr_callDecl->getName()<<"has already been defined.\n";
            }
            else if(curr_callDecl->getName() == print)
                semant_error(curr_callDecl)<<"Function printf can't be defined.";
            else 
                FuncTable[name] = curr_callDecl;  //Decl to call_decl
        }
    }
}

static void install_globalVars(Decls decls) {
    objectEnv.enterscope();
    for (int i = decls->first(); decls->more(i); i = decls->next(i))
    {
        Decl curr_variableDecl = decls->nth(i);

        if(!curr_variableDecl->isCallDecl()){
            Symbol nameglobal = curr_variableDecl->getName();
            Symbol typeglobal = curr_variableDecl->getType();

            if (objectEnv.lookup(nameglobal)) {
                semant_error(curr_variableDecl)<<"Variable"<<curr_variableDecl->getName()<<"has already been defined.\n";
            }
            else 
                objectEnv.addid(nameglobal, new Symbol(typeglobal));
        }
    }
    objectEnv.exitscope();
}

static void check_calls(Decls decls) {
    for (int i = decls->first(); decls->more(i); i = decls->next(i))
    {
        Decl curr_variableDecl = decls->nth(i);
        curr_variableDecl->check();
        
    }
}

static void check_main() {
    if(FuncTable.find(Main) == FuncTable.end()) {
        semant_error()<<"Function main is not defined.\n";
        return ;
    }

    Decl curr_calldecl = FuncTable[Main];
    if (curr_calldecl->getType() != Void ) {
        semant_error(curr_calldecl)<<"Main function should have return type Void.\n";
    }

    CallDecl s = (CallDecl)curr_calldecl;
    if(s->getVariables()->len()!=0) {
        semant_error(s)<<"Function main's parameter should be void.\n";
    }
}

void VariableDecl_class::check() {
    if(this->getType()==Void) {
        semant_error(this)<<"Variable "<<this->getName()<<"\' type can't be Void.\n";
    }
    
    if(objectEnv.lookup(this->getName())) {
        semant_error(this)<<"Variable "<<this->getName()<<" multiply defined.\n";
    } 
    return ;
}

void CallDecl_class::check() {
    CallDecl my_calldecl = this;

    Symbol returnType = my_calldecl->getType();
    if(returnType != Int && returnType != Void && returnType != String && returnType != Float && returnType != Bool)
    {
        semant_error(my_calldecl)<<"Func "<<my_calldecl->getName()<<" shouldn't have return type "<<returnType<<".\n";
    }

    StmtBlock funcBody = my_calldecl->getBody();
    VariableDecls myvaribledecls = funcBody->getVariableDecls();

    objectEnv.enterscope();

    Variables formalparas = this->getVariables();
    for(int a = formalparas->first(); formalparas->more(a); a = formalparas->next(a))
    {
        Variable myvariable = formalparas->nth(a);
        Symbol formalname = myvariable->getName();
        Symbol formaltype = myvariable->getType();
        if(formaltype == Void )
        {
            semant_error(myvariable)<<"The type of formal parameter "<<formalname<< " can't be Void.\n";
        }
        if(objectEnv.lookup(formalname))
        {
            semant_error(myvariable)<<"Formal parameter "<<formalname<<" multiply defined.\n";
        }
        else
            objectEnv.addid(formalname, new Symbol(formaltype));
    }

    for(int k = myvaribledecls->first(); myvaribledecls->more(k); k = myvaribledecls->next(k)) 
    {
        VariableDecl myvaribledecl = myvaribledecls->nth(k);

        Symbol name = myvaribledecl->getName();
        Symbol type = myvaribledecl->getType();

        if(type == Void) {
            semant_error(myvaribledecl)<<"The type of variable "<<name<<" can't be Void.\n";
        }
        if(objectEnv.lookup(name)) {
            semant_error(myvaribledecl)<<"Variable "<<name<<" multiply defined.\n";
        } 
        else objectEnv.addid(name,new Symbol(type));            
    }

    Stmts mystmts = funcBody->getStmts();
    int returncount = 0;
    Stmt mystmt;
    for(int i = mystmts->first(); mystmts->more(i); i = mystmts->next(i)) 
    {
        mystmt = mystmts->nth(i);
        switch (mystmt->stmttypevalue){
        case returnstmtvalue:
            mystmt->check(returnType);
            returncount++;
            break;

        case continuestmtvalue:
            semant_error(mystmt)<<"Continue must be used in a loop sentence.\n";
            break;

        case breakstmtvalue:
            semant_error(mystmt)<<"Break must be used in a loop sentence.\n";
            break;

        default: mystmt->check(returnType);
            break;
        }
    }

    if (returncount == 0) {
        semant_error(mystmt)<<"Function "<<this->getName() <<" must have an overall return statement.\n";
    }

    Variables  parameters = my_calldecl->getVariables();
    if(parameters->len() > 6)
    {
        semant_error(my_calldecl)<<"The total number of parameters should be less than 6.\n";
    }

    objectEnv.exitscope();
}

void StmtBlock_class::check(Symbol type) {

    VariableDecls myvariabledecls = this->getVariableDecls();
    Stmts mystmts = this->getStmts();

    for(int i = myvariabledecls->first(); myvariabledecls->more(i); i = myvariabledecls->next(i))
    {
        VariableDecl check_variabledecl = myvariabledecls->nth(i);
        check_variabledecl->check();
    }

    for(int j = mystmts->first(); mystmts->more(j); j = mystmts->next(j))
    {
        Stmt  mystmt = mystmts->nth(j);

        switch (mystmt->stmttypevalue){
            case returnstmtvalue:
                mystmt->check(type);
                break;

            case continuestmtvalue:
                semant_error(mystmt)<<"Continue must be used in a loop sentence.\n";
                break;

            case breakstmtvalue:
                semant_error(mystmt)<<"Break must be used in a loop sentence.\n";
                break;

            default: mystmt->check(type);
                break;
        }
    }
}

void IfStmt_class::check(Symbol type) {
    if(this->getCondition()->checkType()!=Bool) {
        semant_error(this)<<"if statement's condition must be Bool.\n";
    }

    this->getThen()->check(type);

    if(this->getElse() != stmtBlock(nil_VariableDecls(), nil_Stmts()))
        this->getElse()->check(type);
}

void WhileStmt_class::check(Symbol type) {
    if(this->getCondition()->checkType() != Bool)
    {
        semant_error(this)<<"If statement's condition must be Bool.\n";
    }

    if(this->getBody()!=stmtBlock(nil_VariableDecls(),nil_Stmts()))
    {
        StmtBlock mysytmtBlock = this->getBody();
        Stmts mystmts = mysytmtBlock->getStmts();

        for(int j = mystmts->first(); mystmts->more(j); j = mystmts->next(j))
        {
            Stmt  mystmt = mystmts->nth(j);
            
            switch (mystmt->stmttypevalue){
                case returnstmtvalue:
                    mystmt->check(type);
                    break;

                default: mystmt->check(type);
                    break;
            }
        }
    }
    return ;
}

void ForStmt_class::check(Symbol type) {
    Expr initexpr, condition, loopact;
	StmtBlock body;

    if(this->getInit()!=no_expr())
        this->getInit()->check(type);

    if(this->getLoop()!=no_expr())
        this->getLoop()->check(type);

    if(this->getCondition()!=no_expr())
        this->getCondition()->check(type);

    if(this->getBody()!=stmtBlock(nil_VariableDecls(),nil_Stmts()))
    {
        StmtBlock mysytmtBlock = this->getBody();
        Stmts mystmts = mysytmtBlock->getStmts();

        for(int j=mystmts->first();mystmts->more(j);j=mystmts->next(j))
        {
            Stmt  mystmt = mystmts->nth(j);
    
            switch (mystmt->stmttypevalue){
                case returnstmtvalue:
                    mystmt->check(type);
                    break;

                default: mystmt->check(type);
                    break;
            }  
        }   
    }
}

void ReturnStmt_class::check(Symbol type) {
    Symbol  myreturntype = this->getValue()->checkType();
    if(type != myreturntype ) {
        semant_error(this)<< "Returns " << myreturntype  << ", but need " << type<<".\n";
    }
    return ;
}

void ContinueStmt_class::check(Symbol type) {

}

void BreakStmt_class::check(Symbol type) {

}

Symbol Call_class::checkType(){
    Symbol funcname = this->getName();

    Actuals myactualparas = this->getActuals();

    if(funcname == print){
        if(myactualparas != nil_Actuals()){
            Actual firstactual = myactualparas->nth(1);
            if(firstactual->checkType()!= String) {
                semant_error(this)<<"The type of function printf's first parameter must be String.\n";
            }
        }
        else {
            semant_error(this)<<"Function printf must have at least one parameter.\n";
        }  
    }

    Decl funcdecl = FuncTable[funcname];
    CallDecl real_funcdecl = (CallDecl) funcdecl;
    Variables myformalparas = real_funcdecl->getVariables();
    std::vector<Symbol> formalparatype;

    for(int j = myformalparas->first(); myformalparas->more(j); j = myformalparas->next(j))
    {
        Symbol type = myformalparas->nth(j)->getType();
        formalparatype.push_back(type);
    }

    for(int i = myactualparas->first(); myactualparas->more(i); i = myactualparas->next(i))
    {
        Actual myactual = myactualparas->nth(i);
        Symbol actualtype = myactual->checkType();
        if (actualtype!=formalparatype[i])
            semant_error(this)<<"Function "<<this->getName()<<", the "<<(i+1)<<" parameter should be "<<formalparatype[i]<<" but provided a "<<actualtype<<".\n";
    }
    this->setType(real_funcdecl->getType());

    return real_funcdecl->getType();
}

Symbol Actual_class::checkType(){
    Expr type_ = this->expr;
    this->setType(type_->checkType());
    return  type_->checkType();
}

Symbol Assign_class::checkType(){
    Symbol assignleft = this->lvalue;
    Symbol righttype = this->value->checkType();
    
    if (objectEnv.lookup(assignleft) == NULL) {
        semant_error(this)<<"Assignment to undeclared variable "<<assignleft<<".\n";
        return righttype;
    }

    Symbol lefttype = *objectEnv.lookup(assignleft);
    
    if (!sameType(righttype, lefttype)) {
        semant_error(this)<<"Type "<<righttype<<" of the assigned expression doesn't conform to declared type "<<lefttype<<" of identifier "<<assignleft<<".\n";
        return lefttype;
    }

    this->setType(righttype);
    return righttype;
}

Symbol Add_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();
    
    if(expr1type == Bool || expr2type == Bool){
        semant_error(this)<<"Operation + is only used for numbers whose type is int or float.\n";
        this->setType(Int);       
        return Int;
    }

    else if(expr1type == Float || expr2type == Float){
        this->setType(Float);
        return Float;
    }

    else{
        this->setType(Int);
        return Int;
    }
}

Symbol Minus_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();

    if(expr1type == Bool || expr2type == Bool){
        semant_error(this)<<"Operation - is only used for numbers whose type is int or float.\n";
        this->setType(Int);    
        return Int;
    }

    else if(expr1type == Float || expr2type == Float){
        this->setType(Float);
        return Float;
    }

    else{
        this->setType(Float); 
        return Int;           
    } 
}

Symbol Multi_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();

    if(expr1type == Bool || expr2type == Bool){
        semant_error(this)<<"Operation * is only used for numbers whose type is int or float.\n";
        this->setType(Float);        
        return Float;
    }

    else if(expr1type == Float || expr2type == Float){
        this->setType(Float); 
        return Float;
    }

    else{
        this->setType(Int);  
        return Int;       
    }
}

Symbol Divide_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();
    if(expr1type == Bool || expr2type == Bool){
        semant_error(this)<<"Operation / is only used for numbers whose type is int or float.\n";
        this->setType(Float);
        return Float;
    }

    else if(expr1type == Float || expr2type == Float){
        this->setType(Float);
        return Float;
    }

    else{
        this->setType(Int);       
        return Int;
    }
}

Symbol Mod_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();   

    if(expr1type != Int || expr2type != Int){
        semant_error(this)<<"Operation % is only used between int and int.\n";
        this->setType(Int);
        return Int;
    }

    else{
        this->setType(Int);
        return Int;
    }
}

Symbol Neg_class::checkType(){
    Expr expr = this->e1;
    Symbol exprtype = expr->checkType();

    if(exprtype != Int || exprtype != Float){
        semant_error(this)<<"Only int and float can be negetive.\n";
        return Int;
        this->setType(Int);
    }

    else{
        this->setType(exprtype);
        return exprtype;
    }
}

Symbol Lt_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();

    if(expr1type == Bool || expr2type == Bool){
        semant_error(this)<<"Operation < is only used for numbers whose type is int or float.\n";
        this->setType(Bool);
        return Bool;
    }

    else{
        this->setType(Bool);
        return Bool;
    }
}

Symbol Le_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();
    if(expr1type == Bool || expr2type == Bool){
        semant_error(this)<<"Operation <= is only used for numbers whose type is int  or float.\n";
        this->setType(Bool);
        return Bool;
    }

    else {
            this->setType(Bool);
            return Bool;
    }
}

Symbol Equ_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType(); 

    if (expr1type == Int || expr1type == Float){
        if(expr2type == Bool){
            semant_error(this)<<"Can't execute == between "<<expr1type<<" and "<<expr2type<<".\n";
            this->setType(Bool);
            return Bool;
        }
    }

    if(expr1type == Bool){
        if(expr2type != Bool){
            semant_error(this)<<"Can't execute == between "<<expr1type<<" and "<<expr2type<<".\n";
            this->setType(Bool);
            return Bool;
        }
    } 
    this->setType(Bool);
    return Bool;
}

Symbol Neq_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType(); 

    if (expr1type == Int || expr1type == Float){
        if(expr2type == Bool){
            semant_error(this)<<"Can't execute != between "<<expr1type<<" and "<<expr2type<<".\n";
            this->setType(Bool);
            return Bool;
        }
    }

    if(expr1type == Bool ){
        if(expr2type !=Bool){
            semant_error(this)<<"Can't execute != between "<<expr1type<<" and "<<expr2type<<".\n";
            this->setType(Bool);
            return Bool;
        }
    }     
    this->setType(Bool);
    return Bool;
}

Symbol Ge_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();

    if(expr1type == Bool || expr2type == Bool){
        semant_error(this)<<"Operation >= is only used for numbers whose type is int or float.\n";
        this->setType(Bool);
        return Bool;
    }

    else this->setType(Bool);
        
    return Bool;
}

Symbol Gt_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();

    if(expr1type == Bool || expr2type == Bool){
        semant_error(this)<<"Operation > is only used for numbers whose type is int or float.\n";
        this->setType(Bool);       
        return Bool;
    }

    else this->setType(Bool);

    return Bool;
}

Symbol And_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();

    if(expr1type != Bool || expr2type != Bool ) {
        semant_error(this)<<"Operation && is only used between bool and bool.\n";
        this->setType(Bool);
        return Bool;
    }
    this->setType(Bool);
    return Bool;
}

Symbol Or_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();

    if(expr1type != Bool || expr2type != Bool ){
        semant_error(this)<<"Operation || is only used between bool and bool.\n";
        this->setType(Bool);
        return Bool;
    }
    this->setType(Bool);
    return Bool;
}

Symbol Xor_class::checkType(){
Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();

    if(expr1type != Bool || expr2type != Bool ) {
        semant_error(this)<<"Operation ^ is only used between bool and bool.\n";
        this->setType(Bool);
        return Bool;
    }
    this->setType(Bool);
    return Bool;
}

Symbol Not_class::checkType(){
    Expr expr1 = this->e1;

    if(expr1->checkType() != Bool){
        semant_error(this)<<"Operation ! is only used for bool.\n";
        this->setType(Bool);
        return Bool;
    }
    this->setType(Bool);
    return Bool;
}

Symbol Bitand_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();
    if(expr1type != Int || expr2type != Int ){
        semant_error(this)<<"Operation & is only used between int and int.\n";
        this->setType(Int);
        return Int;
    }
    this->setType(Int);
    return Int; 
}

Symbol Bitor_class::checkType(){
    Expr expr1 = this->e1, expr2 = this->e2;
    Symbol expr1type = expr1->checkType();
    Symbol expr2type = expr2->checkType();
    if(expr1type != Int || expr2type != Int ){
        semant_error(this)<<"Operation | is only used between int and int.\n";
        this->setType(Int);
        return Int;
    }
    this->setType(Int);
    return Int;
}

Symbol Bitnot_class::checkType(){
    Expr expr1 = this->e1;

    if(expr1->checkType() != Int) {
        semant_error(this)<<"Operation ~ is only used for int.\n";
        this->setType(Int);
        return Int;
    }
    this->setType(Int);
    return Int;
}

Symbol Const_int_class::checkType(){
    setType(Int);
    return type;
}

Symbol Const_string_class::checkType(){
    setType(String);
    return type;
}

Symbol Const_float_class::checkType(){
    setType(Float);
    return type;
}

Symbol Const_bool_class::checkType(){
    setType(Bool);
    return type;
}

Symbol Object_class::checkType(){
    Symbol name = this->var;
    Symbol mytype;

    if (objectEnv.lookup(name)){
        mytype = *objectEnv.lookup(name);
    } 
    else{
        semant_error(this)<<"Object "<<name<<" has not been defined.\n";
        this->setType(Int);
        return Int;
    }
    this->setType(mytype);
    return mytype;
}

Symbol No_expr_class::checkType(){
    setType(Void);
    return getType();
}

void Program_class::semant() {
    initialize_constants();
    install_calls(decls);
    check_main();
    install_globalVars(decls);
    check_calls(decls);
    
    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}



