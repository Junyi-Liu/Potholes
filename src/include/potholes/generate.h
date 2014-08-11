/* 
 * File:   codegen.h
 * Author: sb1708
 *
 * Created on July 22, 2013, 5:07 PM
 */

#ifndef CODEGEN_H
#define	CODEGEN_H

#ifdef	__cplusplus
//extern "C" {
#endif

#include <vector>
#include <map>

#include <pet.h>
#include </Users/Junyi/research/HLS/pet/expr.h>
#include </Users/Junyi/research/HLS/pet/tree.h>

/* Appropriate Codegen module */

#include <isl/ast.h>
#include <isl/ast_build.h>

#include <string>

#include <potholes/ast.h>

struct trans_info;
typedef struct trans_info trans_info; 

typedef std::string TypeName;
typedef std::string VarName;
typedef std::map<VarName, TypeName> VarMap;

  

  

std::string pth_generate_scop_name(pet_scop * scop);
VarMap pth_generate_scop_function_prototype_arguments(pet_scop * scop); 
std::vector<std::string> pth_generate_scop_function_invocation_arguments(pet_scop * scop);   
std::string pth_generate_scop_function_invocation(pet_scop * scop, std::string name);
std::string pth_generate_scop_function_declaration(pet_scop * scop, std::string name);
std::string pth_generate_scop_function_replace(pet_scop * scop, std::string name, isl_set * param);
  void pth_generate_initialize(isl_ctx * );      

pth_stmt * pth_get_scop_statement_by_id(pth_scop *, pth_id *);
pth_stmt * pth_get_scop_statement_by_name(pth_scop *, pth_id *);
   

pth_ast_stmt * pth_generate_ast_stmt(pth_ast_build *, pth_scop *, pth_id *); // scop has an id from pet domain
pth_ast_stmt * pth_generate_ast_stmt_call(pth_ast_build *, pth_scop *, pth_id * id);
pth_ast_stmt * pth_generate_ast_stmt_assign(pth_ast_build *, pth_scop *, pth_id * id);      

isl_ast_expr * pth_generate_ast_expr(pth_ast_build *, pth_scop *, pth_stmt *, pth_expr *);
isl_ast_expr * pth_generate_ast_expr_binary(pth_ast_build*, pth_scop*, pth_stmt*, pth_expr*);
isl_ast_expr * pth_generate_ast_expr_arith(pth_ast_build*, pth_scop*, pth_stmt*, pth_expr*, pet_op_type);
isl_ast_expr * pth_generate_ast_expr_relational(pth_ast_build*, pth_scop*, pth_stmt*, pth_expr*);
isl_ast_expr * pth_generate_ast_expr_unary(pth_ast_build*, pth_scop*, pth_stmt*, pth_expr*);
isl_ast_expr * pth_generate_ast_expr_access(pth_ast_build*, pth_scop*, pth_stmt*, pth_expr*);
isl_ast_expr * pth_generate_ast_expr_call(pth_ast_build*, pth_scop*, pth_stmt*, pth_expr*);


int check_bset(isl_basic_set * bset, void *user);
int check_constraint(isl_constraint * c, void *user);

__isl_give isl_ast_expr *isl_ast_expr_alloc_int_si(isl_ctx *ctx, int i);
__isl_give isl_ast_expr *isl_ast_expr_alloc_binary(enum isl_ast_op_type type, __isl_take isl_ast_expr *expr1, __isl_take isl_ast_expr *expr2);
int isl_ast_build_aff_is_nonneg(__isl_keep isl_ast_build *build, __isl_keep isl_aff *aff);
__isl_give isl_id *isl_ast_build_get_iterator_id(__isl_keep isl_ast_build *build, int pos);

__isl_give isl_ast_node *isl_ast_node_alloc_if(__isl_take isl_ast_expr *guard);
  
#ifdef	__cplusplus
//}
#endif

#endif	/* CODEGEN_H */

