#include <isl/space.h>

#include <isl/ast.h>
#include <isl/ast_build.h>
#include <isl/map.h>
#include <isl/aff.h>
#include <isl/ilp.h>

#include <pet.h>
#include </Users/Junyi/research/HLS/pet/expr.h>

#include <iostream>

#include <potholes/statement.h>
#include <potholes/ast.h>
#include <potholes/generate.h>

#include <cassert>
#include <cstring>

struct pth_access_t {
public:
  isl_map * access;
  int read;
  int write;
    
  pth_access_t(pet_expr * expr) {
        
    // check type of expr or throw exception
    access = pet_expr_access_get_dependent_access(expr);
    //read = pet_expr_access_is_read(expr);
    //write = pet_expr_access_is_write(expr);
    
    //access = (expr->acc).access;
    read = (expr->acc).read;
    write = (expr->acc).write;
  }
    
};



isl_ast_expr * pth_build_ast_expr_from_aff(isl_aff * aff, pth_ast_build * build);
int pth_ast_build_aff_is_nonneg(pth_ast_build *build, isl_aff *aff);

isl_ast_expr *ast_expr_sub(isl_ast_expr *expr1, isl_ast_expr *expr2);



isl_val * pth_get_dim_size(isl_set * set, unsigned dim)
{
  //   std::cerr << "Getting Dim " <<  dim << " " << "\n";
  // project out top dimension
    
  //    isl_space * space = isl_set_get_space(set);
    
  //  isl_local_space * local_space = isl_local_space_from_space(space);

 
  isl_set * bounded_set = isl_set_project_out(isl_set_copy(set), isl_dim_set, 0, dim);
  
  isl_space * bounded_space = isl_set_get_space(bounded_set);
  isl_aff * aff = isl_aff_zero_on_domain(isl_local_space_from_space(bounded_space));
  aff = isl_aff_set_coefficient_si(aff, isl_dim_in, 0, 1);
   
  isl_val * max = isl_set_max_val(bounded_set, aff);
  
  isl_aff_free(aff);
  return isl_val_add_ui(max, 1);
}

isl_aff * pth_create_flattening_aff(isl_set * bs,  unsigned size) {
  isl_space * space = isl_set_get_space(bs);
    
    
    
  isl_local_space * local_space = isl_local_space_from_space(isl_space_copy(space));
    

  //            isl_printer * printer = isl_printer_to_str(isl_local_space_get_ctx(local_space));
    
  isl_ctx * ctx = isl_local_space_get_ctx(local_space);
        
        
  //	space = isl_local_space_add_dims(space, isl_dim_param, params);
  isl_aff * affine_mapping = isl_aff_zero_on_domain(isl_local_space_copy(local_space));
        
       
        
  //   printer = isl_printer_print_aff(printer, affine_mapping);
  //         std::cerr << isl_printer_get_str(printer) << std::endl;
                
    
        
  int i;
       
  //i,j   c0 = i, c1 = j
  //i,k   c0 = i, c1 = j, c2 = k
  //k,j
        

  //isl_val * num = isl_val_int_from_ui(ctx, size);
  isl_val * num = isl_val_one(ctx);
  for (i =  0 ; i < isl_local_space_dim(local_space, isl_dim_out)   ; i++)
    {	
      affine_mapping =isl_aff_set_coefficient_val(affine_mapping, isl_dim_in, isl_local_space_dim(local_space, isl_dim_out) - i - 1, isl_val_copy(num));
              
      if ((i + 1) < isl_local_space_dim(local_space, isl_dim_out) ) {
	num = isl_val_mul(num, pth_get_dim_size(bs, isl_local_space_dim(local_space, isl_dim_out) - i - 1)); 	
      }
                
    }
  //std::cerr << "i is " << i << "\n";quit
  //    return isl_map_from_aff(affine_mapping);
  //isl_aff_dump(affine_mapping);
  return affine_mapping;
}

isl_aff * pth_flatten_expr_access(pet_scop * scop , isl_map * access , isl_id * id ) {
    
  isl_map_free(access);

  for (int i = 0 ; i < scop->n_array ; i++) {
    pet_array * array = scop->arrays[i];
        
    isl_set * extent = isl_set_copy(array->extent);
    isl_space * space = isl_set_get_space(extent);
        
    if (isl_space_has_tuple_id(space, isl_dim_set)) {
            
      if (isl_space_get_tuple_id(space, isl_dim_set) == id) { 
                
	isl_aff * flattening_aff = pth_create_flattening_aff(extent, array->element_size);

	// extent free?
	isl_space_free(space);
	isl_id_free(id);
	return flattening_aff;
             
      }
    }

    isl_space_free(space);
    isl_set_free(extent);
  }

  isl_id_free(id);
  return NULL;
}


void pth_print_aff(isl_aff * pa) {
  isl_space * space = isl_aff_get_space(pa);
  isl_local_space * local_space = isl_local_space_from_space(space);
  isl_printer * printer = isl_printer_to_str(isl_local_space_get_ctx(local_space));
  printer = isl_printer_print_aff(printer, pa);
  std::cerr << isl_printer_get_str(printer) <<"\n";
  isl_printer_free(printer);
}

/* Does "expr" represent the zero integer?
 */
static int ast_expr_is_zero(isl_ast_expr *expr)
{
  if (!expr)
    return -1;
  if (isl_ast_expr_get_type(expr) != isl_ast_expr_int)
    return 0;
  return isl_val_is_zero(isl_ast_expr_get_val(expr));
}

isl_aff *oppose_div_arg( isl_aff *aff, isl_val *d)
{
  aff = isl_aff_neg(aff);
  aff = isl_aff_add_constant_val(aff, d);
  aff = isl_aff_add_constant_si(aff, -1);

  return aff;
}

/* Create an expression representing the sum of "expr1" and "expr2",
 * provided neither of the two expressions is identically zero.
 */

int pth_ast_build_aff_is_nonneg(pth_ast_build *build, isl_aff *aff)
{
  isl_set *test;
  int empty;

  if (!build)
    return -1;

  aff = isl_aff_copy(aff);
  test = isl_set_from_basic_set(isl_aff_neg_basic_set(aff));
  test = isl_set_intersect(test, isl_set_copy(build->domain));
  empty = isl_set_is_empty(test);
  isl_set_free(test);

  return empty;
}

static __isl_give isl_ast_expr *isl_ast_expr_mod(__isl_keep isl_val *v,
						 __isl_keep isl_aff *aff, __isl_keep isl_val *d,
						 __isl_keep pth_ast_build *build)
{
  isl_ctx *ctx;
  isl_ast_expr *expr;
  isl_ast_expr *c;

  if (!aff)
    return NULL;

  ctx = isl_aff_get_ctx(aff);
  expr = pth_build_ast_expr_from_aff(isl_aff_copy(aff), build);

  c = isl_ast_expr_from_val(isl_val_copy(d));
  expr = pth_ast_expr_to_isl_ast_expr(pth_ast_expr_alloc_binary(isl_ast_op_pdiv_r, expr, c));

  if (!isl_val_is_one(v)) {
    c = isl_ast_expr_from_val(isl_val_copy(v));
    expr = isl_ast_expr_mul(c, expr);
  }

  return expr;
}

static __isl_give isl_ast_expr *ast_expr_add(__isl_take isl_ast_expr *expr1,
					     __isl_take isl_ast_expr *expr2)
{
  if (!expr1 || !expr2)
    goto error;

  if (ast_expr_is_zero(expr1)) {
    isl_ast_expr_free(expr1);
    return expr2;
  }

  if (ast_expr_is_zero(expr2)) {
    isl_ast_expr_free(expr2);
    return expr1;
  }

  return isl_ast_expr_add(expr1, expr2);
 error:
  isl_ast_expr_free(expr1);
  isl_ast_expr_free(expr2);
  return NULL;
}

/* Create an isl_ast_expr that scales "expr" by "v".
 *
 * If v is 1, we simply return expr.
 * If v is -1, we return
 *
 *	(isl_ast_op_minus, expr)
 *
 * Otherwise, we return
 *
 *	(isl_ast_op_mul, expr(v), expr)
 */
static __isl_give isl_ast_expr *scale(__isl_take isl_ast_expr *expr,
				      __isl_take isl_val *v)
{
  isl_ast_expr *c;

  if (!expr || !v)
    goto error;
  if (isl_val_is_one(v)) {
    isl_val_free(v);
    return expr;
  }

  if (isl_val_is_negone(v)) {
    isl_val_free(v);
    expr = isl_ast_expr_neg(expr);
  } else {
    c = isl_ast_expr_from_val(v);
    expr = isl_ast_expr_mul(c, expr);
  }

  return expr;
 error:
  isl_val_free(v);
  isl_ast_expr_free(expr);
  return NULL;
}

/* Create an isl_ast_expr evaluating the div at position "pos" in "ls".
 * The result is simplified in terms of build->domain.
 *
 * *change_sign is set by this function if the sign of
 * the expression has changed.
 * "ls" is known to be non-NULL.
 *
 * Let the div be of the form floor(e/d).
 * If the ast_build_prefer_pdiv option is set then we check if "e"
 * is non-negative, so that we can generate
 *
 *	(pdiv_q, expr(e), expr(d))
 *
 * instead of
 *
 *	(fdiv_q, expr(e), expr(d))
 *
 * If the ast_build_prefer_pdiv option is set and
 * if "e" is not non-negative, then we check if "-e + d - 1" is non-negative.
 * If so, we can rewrite
 *
 *	floor(e/d) = -ceil(-e/d) = -floor((-e + d - 1)/d)
 *
 * and still use pdiv_q.
 */
static __isl_give isl_ast_expr *var_div(int *change_sign,
					__isl_keep isl_local_space *ls,
					int pos, __isl_keep pth_ast_build *build)
{
  isl_ctx *ctx = isl_local_space_get_ctx(ls);
  isl_aff *aff;
  isl_ast_expr *num, *den;
  isl_val *d;
  enum isl_ast_op_type type;

  aff = isl_local_space_get_div(ls, pos);
  d = isl_aff_get_denominator_val(aff);
  aff = isl_aff_scale_val(aff, isl_val_copy(d));
  den = isl_ast_expr_from_val(isl_val_copy(d));

  type = isl_ast_op_fdiv_q;
  if (isl_options_get_ast_build_prefer_pdiv(ctx)) {
    int non_neg = pth_ast_build_aff_is_nonneg(build, aff);
    if (non_neg >= 0 && !non_neg) {
      isl_aff *opp = oppose_div_arg(isl_aff_copy(aff),
				    isl_val_copy(d));
      non_neg = pth_ast_build_aff_is_nonneg(build, opp);
      if (non_neg >= 0 && non_neg) {
	*change_sign = 1;
	isl_aff_free(aff);
	aff = opp;
      } else
	isl_aff_free(opp);
    }
    if (non_neg < 0)
      aff = (isl_aff *)isl_aff_free(aff);
    else if (non_neg)
      type = isl_ast_op_pdiv_q;
  }

  isl_val_free(d);
  num = pth_build_ast_expr_from_aff(aff, build);
  return pth_ast_expr_to_isl_ast_expr(pth_ast_expr_alloc_binary(type, num, den));
}


/* Create an isl_ast_expr evaluating the specified dimension of "ls".
 * The result is simplified in terms of build->domain.
 *
 * *change_sign is set by this function if the sign of
 * the expression has changed.
 *
 * The isl_ast_expr is constructed based on the type of the dimension.
 * - divs are constructed by var_div
 * - set variables are constructed from the iterator isl_ids in "build"
 * - parameters are constructed from the isl_ids in "ls"
 */
isl_ast_expr *var(int *change_sign, isl_local_space *ls,
		  enum isl_dim_type type, int pos, __isl_keep pth_ast_build *build)
{
  isl_ctx *ctx = isl_local_space_get_ctx(ls);
  isl_id *id;

  if (type == isl_dim_div)
    return var_div(change_sign, ls, pos, build);

  if (type == isl_dim_set) {
    id = pth_ast_build_get_iterator_id(build, pos);
    return isl_ast_expr_from_id(id);
  }

  if (!isl_local_space_has_dim_id(ls, type, pos))
    isl_die(ctx, isl_error_internal, "unnamed dimension",
	    return NULL);
  id = isl_local_space_get_dim_id(ls, type, pos);
  return isl_ast_expr_from_id(id);
}

/* Add an expression for "*v" times the specified dimension of "ls"
 * to expr.
 *
 * Let e be the expression for the specified dimension,
 * multiplied by the absolute value of "*v".
 * If "*v" is negative, we create
 *
 *	(isl_ast_op_sub, expr, e)
 *
 * except when expr is trivially zero, in which case we create
 *
 *	(isl_ast_op_minus, e)
 *
 * instead.
 *
 * If "*v" is positive, we simply create
 *
 *	(isl_ast_op_add, expr, e)
 *
 */
isl_ast_expr *isl_ast_expr_add_term(
				    isl_ast_expr *expr,
				    isl_local_space *ls, enum isl_dim_type type, int pos,
				    isl_val *v, __isl_keep pth_ast_build *build)
{
  isl_ast_expr *term;
  int change_sign;

  if (!expr)
    return NULL;

  change_sign = 0;
  term = var(&change_sign, ls, type, pos, build);
  if (change_sign)
    v = isl_val_neg(v);

  if (isl_val_is_neg(v) && !ast_expr_is_zero(expr)) {
    v = isl_val_neg(v);
    term = scale(term, v);
    return ast_expr_sub(expr, term);
  } else {
    term = scale(term, v);
    return ast_expr_add(expr, term);
  }
}

/* Add an expression for "v" to expr.
 */
static __isl_give isl_ast_expr *isl_ast_expr_add_int(
						     __isl_take isl_ast_expr *expr, __isl_take isl_val *v)
{
  isl_ctx *ctx;
  isl_ast_expr *expr_int;

  if (!expr || !v)
    goto error;

  if (isl_val_is_zero(v)) {
    isl_val_free(v);
    return expr;
  }

  ctx = isl_ast_expr_get_ctx(expr);
  if (isl_val_is_neg(v) && !ast_expr_is_zero(expr)) {
    v = isl_val_neg(v);
    expr_int = isl_ast_expr_from_val(v);
    return ast_expr_sub(expr, expr_int);
  } else {
    expr_int = isl_ast_expr_from_val(v);
    return ast_expr_add(expr, expr_int);
  }
 error:
  isl_ast_expr_free(expr);
  isl_val_free(v);
  return NULL;
}

/* Subtract expr2 from expr1.
 *
 * If expr2 is zero, we simply return expr1.
 * If expr1 is zero, we return
 *
 *	(isl_ast_op_minus, expr2)
 *
 * Otherwise, we return
 *
 *	(isl_ast_op_sub, expr1, expr2)
 */
isl_ast_expr *ast_expr_sub(__isl_take isl_ast_expr *expr1,isl_ast_expr *expr2)
{
  if (!expr1 || !expr2)
    goto error;

  if (ast_expr_is_zero(expr2)) {
    isl_ast_expr_free(expr2);
    return expr1;
  }

  if (ast_expr_is_zero(expr1)) {
    isl_ast_expr_free(expr1);
    return isl_ast_expr_neg(expr2);
  }

  return isl_ast_expr_sub(expr1, expr2);
 error:
  isl_ast_expr_free(expr1);
  isl_ast_expr_free(expr2);
  return NULL;
}

isl_aff *extract_rational( isl_aff *aff,
			   isl_ast_expr **expr, pth_ast_build *build)
{
  int i, j, n;
  isl_aff *rat = NULL;
  isl_local_space *ls = NULL;
  isl_ast_expr *rat_expr;
  isl_val *v, *d;
  enum isl_dim_type t[] = { isl_dim_param, isl_dim_in, isl_dim_div };
  enum isl_dim_type l[] = { isl_dim_param, isl_dim_set, isl_dim_div };

  if (!aff)
    return NULL;
  d = isl_aff_get_denominator_val(aff);
  if (!d)
    goto error;
  if (isl_val_is_one(d)) {
    isl_val_free(d);
    return aff;
  }

  aff = isl_aff_scale_val(aff, isl_val_copy(d));

  ls = isl_aff_get_domain_local_space(aff);
  rat = isl_aff_zero_on_domain(isl_local_space_copy(ls));

  for (i = 0; i < 3; ++i) {
    n = isl_aff_dim(aff, t[i]);
    for (j = 0; j < n; ++j) {
      isl_aff *rat_j;

      v = isl_aff_get_coefficient_val(aff, t[i], j);
      if (!v)
	goto error;
      if (isl_val_is_divisible_by(v, d)) {
	isl_val_free(v);
	continue;
      }
      rat_j = isl_aff_var_on_domain(isl_local_space_copy(ls),
				    l[i], j);
      rat_j = isl_aff_scale_val(rat_j, v);
      rat = isl_aff_add(rat, rat_j);
    }
  }

  v = isl_aff_get_constant_val(aff);
  if (isl_val_is_divisible_by(v, d)) {
    isl_val_free(v);
  } else {
    isl_aff *rat_0;

    rat_0 = isl_aff_val_on_domain(isl_local_space_copy(ls), v);
    rat = isl_aff_add(rat, rat_0);
  }

  isl_local_space_free(ls);

  aff = isl_aff_sub(aff, isl_aff_copy(rat));
  aff = isl_aff_scale_down_val(aff, isl_val_copy(d));

  rat_expr = pth_build_ast_expr_from_aff(rat, build);
  rat_expr = isl_ast_expr_div(rat_expr, isl_ast_expr_from_val(d));
  *expr = ast_expr_add(*expr, rat_expr);

  return aff;
 error:
  isl_aff_free(rat);
  isl_local_space_free(ls);
  isl_aff_free(aff);
  isl_val_free(d);
  return NULL;
}


isl_aff *extract_modulo( isl_aff *aff,
			 isl_ast_expr **pos, isl_ast_expr **neg,
			 pth_ast_build *build, int j,  isl_val *v)
{
  isl_ast_expr *expr;
  isl_aff *div;
  int s;
  int mod;
  isl_val *d;

  div = isl_aff_get_div(aff, j);
  d = isl_aff_get_denominator_val(div);
  mod = isl_val_is_divisible_by(v, d);
  if (mod) {
    div = isl_aff_scale_val(div, isl_val_copy(d));
    mod = pth_ast_build_aff_is_nonneg(build, div);
    if (mod >= 0 && !mod) {
      isl_aff *opp = oppose_div_arg(isl_aff_copy(div),
				    isl_val_copy(d));
      mod = pth_ast_build_aff_is_nonneg(build, opp);
      if (mod >= 0 && mod) {
	isl_aff_free(div);
	div = opp;
	v = isl_val_neg(v);
      } else
	isl_aff_free(opp);
    }
  }
  if (mod < 0) {
    isl_aff_free(div);
    isl_val_free(d);
    isl_val_free(v);
    return (isl_aff *)isl_aff_free(aff);
              
  } else if (!mod) {
    isl_aff_free(div);
    isl_val_free(d);
    isl_val_free(v);
    return aff;
  }
  v = isl_val_div(v, isl_val_copy(d));
  s = isl_val_sgn(v);
  v = isl_val_abs(v);
  expr = isl_ast_expr_mod(v, div, d, build);
  isl_val_free(d);
  if (s > 0)
    *neg = ast_expr_add(*neg, expr);
  else
    *pos = ast_expr_add(*pos, expr);
  aff = isl_aff_set_coefficient_si(aff, isl_dim_div, j, 0);
  if (s < 0)
    v = isl_val_neg(v);
  div = isl_aff_scale_val(div, v);
  d = isl_aff_get_denominator_val(aff);
  div = isl_aff_scale_down_val(div, d);
  aff = isl_aff_add(aff, div);

  return aff;
}

isl_aff * extract_modulos(isl_aff *aff,
			  isl_ast_expr **pos,  isl_ast_expr **neg,
			  pth_ast_build *build)
{
  isl_ctx *ctx;
  int j, n;

  if (!aff)
    return NULL;

  ctx = isl_aff_get_ctx(aff);
  if (!isl_options_get_ast_build_prefer_pdiv(ctx))
    return aff;

  n = isl_aff_dim(aff, isl_dim_div);
  for (j = 0; j < n; ++j) {
    isl_val *v;

    v = isl_aff_get_coefficient_val(aff, isl_dim_div, j);
    if (!v)
      return (isl_aff *)isl_aff_free(aff);
    if (isl_val_is_zero(v) ||
	isl_val_is_one(v) || isl_val_is_negone(v)) {
      isl_val_free(v);
      continue;
    }
    aff = extract_modulo(aff, pos, neg, build, j, v);
    if (!aff)
      break;
  }

  return aff;
}

isl_ast_expr * pth_build_ast_expr_from_aff(isl_aff * aff, pth_ast_build * build) { 
    
  
  int i, j;
  int n;
  isl_val *v;
  isl_ctx *ctx = isl_aff_get_ctx(aff);
  isl_ast_expr *expr, *expr_neg;
  enum isl_dim_type t[] = { isl_dim_param, isl_dim_in, isl_dim_div };
  enum isl_dim_type l[] = { isl_dim_param, isl_dim_set, isl_dim_div };
  isl_local_space *ls;

  if (!aff)
    return NULL;  

  expr = pth_ast_expr_to_isl_ast_expr(pth_ast_expr_alloc_int_si(ctx, 0));
  expr_neg = pth_ast_expr_to_isl_ast_expr(pth_ast_expr_alloc_int_si(ctx, 0));

  aff = extract_rational(aff, &expr, build);

  aff = extract_modulos(aff, &expr, &expr_neg, build);
  expr = ast_expr_sub(expr, expr_neg);  

  ls = isl_aff_get_domain_local_space(aff);
  
  //std::cout<< "depth: "<<build->depth<<std::endl;

  for (i = 0; i < 3; ++i) {
    n = isl_aff_dim(aff, t[i]);   
    for (j = 0; j < n; ++j) {
      v = isl_aff_get_coefficient_val(aff, t[i], j);
      if (!v)
	expr = (isl_ast_expr *)isl_ast_expr_free(expr);
      if (isl_val_is_zero(v)) {
	isl_val_free(v);
	continue;
      }
      // avoid to exceed pos bound
      if( j > build->depth-1 ){
	// always use last pos
	expr = isl_ast_expr_add_term(expr, ls, l[i], build->depth-1, v, build);
      }
      else{
	// normal pos
	expr = isl_ast_expr_add_term(expr, ls, l[i], j, v, build);
      }
    }
  }

  v = isl_aff_get_constant_val(aff);
  expr = isl_ast_expr_add_int(expr, v);

  isl_local_space_free(ls);
  isl_aff_free(aff);

  return expr;
}

typedef struct {
  struct pth_ast_build * build;
  isl_ast_expr_list * indices;
  isl_id * tuple_id;
  pth_scop * scop;
   
} pth_ast_build_with_isl_ast_expr_list ;

int pth_generate_access_expr_ast(isl_set * set, isl_multi_aff * maff, void * user) { 
    
  isl_space * space = isl_set_get_space(set);
  isl_local_space * local_space = isl_local_space_from_space(space);
   
  isl_ctx * ctx = isl_local_space_get_ctx(local_space);
    
  // isl_printer * mprinter = isl_printer_to_str(isl_local_space_get_ctx(local_space));
  // mprinter = isl_printer_set_output_format(mprinter, ISL_FORMAT_ISL);

  pth_ast_build_with_isl_ast_expr_list * args = (pth_ast_build_with_isl_ast_expr_list *)(user);
  
  unsigned dim_count = isl_multi_aff_dim(maff, isl_dim_out);
  args->indices = isl_ast_expr_list_alloc(ctx, 1);
  
  isl_id * offset_id = pth_array_offset_lookup(args->scop->array_offsets, args->tuple_id);
    
  for (unsigned i = 0 ; i < isl_multi_aff_dim(maff, isl_dim_out)  ; i++) {
    isl_aff * aff = isl_multi_aff_get_aff(maff, i);
    //           mprinter = isl_printer_print_aff(mprinter, aff);
    //          mprinter = isl_printer_print_str(mprinter, "\n\n");
    // mprinter = isl_printer_print_union_map(mprinter, args->build->executed);
    // std::cerr << isl_printer_get_str(mprinter) << "\n";
    isl_ast_expr * ast_expr = pth_build_ast_expr_from_aff(aff, args->build);
    // ast_expr = isl_ast_expr_add(isl_ast_expr_from_id(offset_id), ast_expr);
    args->indices = isl_ast_expr_list_add(args->indices, ast_expr);
  }
 
  return 0;
}

int pth_generate_access_map_expr_ast(isl_map * amap, void * user) {
     
  pth_ast_build_with_isl_ast_expr_list * args = (pth_ast_build_with_isl_ast_expr_list *)(user);
  isl_id * memory_space_id = pth_memory_space_id();
  amap =  isl_map_set_tuple_id(amap, isl_dim_out, isl_id_copy(memory_space_id) );  
  
  //isl_id_dump(memory_space_id);
  //isl_map_dump(amap);

  isl_pw_multi_aff * pwma = isl_pw_multi_aff_from_map(amap);
  int success = isl_pw_multi_aff_foreach_piece(pwma, pth_generate_access_expr_ast, args);
  return success;
}

int pth_generate_v_ast(isl_set * set, isl_multi_aff * maff, void * user) {

  pth_ast_build_with_isl_ast_expr_list * args = (pth_ast_build_with_isl_ast_expr_list *)(user);
  
  // create ast expression list
  isl_space * space = isl_set_get_space(set);
  isl_local_space * local_space = isl_local_space_from_space(space); 
  isl_ctx * ctx = isl_local_space_get_ctx(local_space);
  args->indices = isl_ast_expr_list_alloc(ctx, 1);
 
  //std::cout<< "multi_aff dim: "<< isl_multi_aff_dim(maff, isl_dim_out)<< std::endl;

  // take out 1st affine
  isl_aff * aff = isl_multi_aff_get_aff(maff, 0);
  isl_aff_dump(aff);
  
  // build ast expression from affine
  isl_ast_expr * ast_expr = pth_build_ast_expr_from_aff(aff, args->build);
  isl_ast_expr_dump(ast_expr);
  
  // insert expression
  args->indices = isl_ast_expr_list_add(args->indices, ast_expr);
  
  return 0;
} 

isl_ast_expr * ast_expr_op_arg_replace(isl_ast_expr * expr, isl_ast_expr ** list, int * n_list){
   int n_arg;
   isl_ast_expr * arg;
   int expr_type = isl_ast_expr_get_type(expr);

   if(expr_type == 0){ //expr: op
     n_arg = isl_ast_expr_get_op_n_arg(expr);
     // traverse all op args
     for(int i=n_arg; i>0; i--){
       arg = isl_ast_expr_get_op_arg(expr, i-1);
       arg = ast_expr_op_arg_replace(arg, list, n_list);
       isl_ast_expr_dump(arg);
       expr = isl_ast_expr_set_op_arg(expr, i-1, arg);
     }
   }
   else if(expr_type == 1){ //expr: id
     if(*n_list > 0){
       // replace node
       expr = list[*n_list-1];
       *n_list = *n_list-1;
     }
   }
   
   //isl_ast_expr_dump(expr);
   // no operation for expr:int
   return expr;

 }

typedef struct {
  int n;
  int src[1];
} id_record ;

isl_ast_expr * pth_generate_wrapped_access_expr(pth_ast_build * build, pth_scop * scop, pth_stmt * stmt, pth_expr * expr ) {   

  //Check arguments of access
  //pet_expr_dump(expr);  
  std::cout<< "#####access args number: " << expr->n_arg << std::endl;
  
  // Put arguments into a list of isl_ast_expr
  isl_ast_expr * expr_list[expr->n_arg];
  for(int i=0; i < expr->n_arg ; i++){
    //pet_expr_dump(expr->args[i]);
    expr_list[i] = pth_generate_ast_expr(build, scop, stmt, expr->args[i]);
    isl_ast_expr_dump(expr_list[i]);
  }
  
  std::cout<< "000000*************************" <<std::endl;
  // record iterator positions
  // This is a better solution: use build->values
  id_record user;
  user.n = 0;

  isl_multi_aff_dump(build->values);

  isl_aff * it_aff;
  isl_val * co;

  for(int i=0; i<build->depth; i++){
   it_aff = isl_multi_aff_get_aff(build->values, i); 
   co = isl_aff_get_coefficient_val(it_aff, isl_dim_in, i);
   //isl_aff_dump(it_aff);
   //isl_val_dump(co);
   
   // record non-zero dims
   if(isl_val_is_zero(co) == 0){
     user.src[user.n] = i;
     user.n = user.n+1;
     //std::cout<< "recording src pos: " << i <<std::endl;
   }
   isl_val_free(co);
   isl_aff_free(it_aff);
  }

  //assert(false);  

  //isl_union_map_foreach_map(build->executed, detect_src_id_map, &user);
  //std::cout<< "non-zero dims number: " << user.n <<std::endl;
  std::cout<< "000000*************************" <<std::endl;

  //assert(false);
  
  // get map and space
  pth_access_t access_info(expr);
  isl_map * map = isl_map_copy(access_info.access);
  //isl_space * access_space = isl_map_get_space(map);

  // creat access affine
  isl_map * tmap = isl_map_copy(map);
  isl_space * access_space = isl_map_get_space(map);
  isl_id * tid = isl_space_get_tuple_id(access_space, isl_dim_out);

  isl_aff * acc_aff = pth_flatten_expr_access(scop->scop, tmap, tid); 
  isl_map * acc_map = isl_map_from_pw_aff(isl_pw_aff_from_aff(acc_aff)); 
  acc_map = isl_map_apply_range(isl_map_copy(map), acc_map);
  isl_map_dump(acc_map); 

  std::cout<< "222222*************************" <<std::endl;
  acc_map = isl_map_flatten_domain(acc_map);
  //isl_map_dump(acc_map);

  // insert dummy dims
  // can replace the old method with apply_range functions
  int m = 0;
  for(int i=0; i<user.n ;i++){    
    acc_map = isl_map_insert_dims(acc_map, isl_dim_in, i+m, user.src[i]-i-m);
    m = user.src[i]-i;    
  }
  //isl_map_dump(acc_map);
  std::cout<< "222222*************************" <<std::endl;  


  isl_pw_multi_aff * acc_pwma = isl_pw_multi_aff_from_map(acc_map);
  //isl_pw_multi_aff_dump(acc_pwma);

  // generate ast exprssion list for access affine
  pth_ast_build_with_isl_ast_expr_list args;
  args.build = build;
  args.scop = scop;

  // Append "_flt" for the new array pointer for flattened access
  std::string name(isl_space_get_tuple_name(access_space, isl_dim_out), strlen(isl_space_get_tuple_name(access_space, isl_dim_out)));
  name.append("_flt");    
  access_space = isl_space_set_tuple_name(access_space, isl_dim_out, name.c_str());

  args.tuple_id = isl_space_get_tuple_id(access_space, isl_dim_out);
  int success = isl_pw_multi_aff_foreach_piece(acc_pwma, pth_generate_v_ast, &args);
    
  // check ast exprssion list number
  //int list_n = isl_ast_expr_list_n_ast_expr(args.indices);
  //std::cout<< "################## affine list_n: "<< list_n << std::endl;
  
  //take out isl_ast_expr of access expression 
  isl_ast_expr * acc_expr = isl_ast_expr_list_get_ast_expr(args.indices, 0);
  //isl_ast_expr_dump(acc_expr);    

  int n_list = expr->n_arg; 
  // replace op args with the elements of the list recursively
  acc_expr = ast_expr_op_arg_replace(acc_expr, expr_list, &n_list);
  //std::cout<< "################## n_list: "<<n_list <<std::endl;
  //isl_ast_expr_dump(acc_expr);
 
  // generate final access expression AST
  isl_ast_expr * access_id = isl_ast_expr_from_id(isl_id_copy(args.tuple_id));   
  args.indices = isl_ast_expr_list_set_ast_expr(args.indices, 0, acc_expr);
  isl_ast_expr * access = isl_ast_expr_access(access_id, args.indices); 
  isl_ast_expr_dump(access);

  return access;
  //assert(false);

}


isl_ast_expr * pth_generate_access_expr(pth_ast_build * build, pth_scop * scop, pth_stmt * stmt, pth_expr * expr ) {

  // isl_ast_expr * access = isl_ast_expr_from_val(isl_val_zero(ctx));   
  isl_ast_expr * access = NULL;

  // check build
  //std::cout<< "%%%%%%%%%%%%%%%%%%%%%%%%%%%" <<std::endl;
  //isl_multi_aff_dump(build->values);
  //isl_id_list_dump(build->iterators);
  //std::cout<< "depth: "<< build->depth <<std::endl;
  //std::cout<< "%%%%%%%%%%%%%%%%%%%%%%%%%%%" <<std::endl;
  //assert(false);

  if(expr->n_arg > 0){
    access = pth_generate_wrapped_access_expr(build, scop, stmt, expr);
    return access;
  }

  pth_access_t access_info(expr);
  isl_map * map = access_info.access;
  isl_space * access_space = isl_map_get_space(map);

  isl_ctx * ctx = isl_local_space_get_ctx(isl_local_space_from_space(isl_space_copy(access_space)));
  isl_printer * mprinter = isl_printer_to_str(ctx);
  mprinter = isl_printer_set_output_format(mprinter, ISL_FORMAT_ISL);
         
  bool has_tuple_id = isl_space_has_tuple_id(access_space, isl_dim_out);
  //std::cout<<"access_space has tuple id: "<< has_tuple_id << std::endl;  

  isl_map_dump(map);
       
  if (has_tuple_id) {
     
    isl_aff * aff = pth_flatten_expr_access(scop->scop,  isl_map_copy(map),  isl_id_copy(isl_space_get_tuple_id(access_space, isl_dim_out))); 
    isl_map * amap = isl_map_from_pw_aff(isl_pw_aff_from_aff(aff));
    isl_space * space = isl_map_get_space(amap);
    
    isl_map_dump(amap);
    amap = isl_map_apply_range(isl_map_copy(map), amap);
    isl_map_dump(amap);

    // align tuple id
    isl_id * st_id = isl_set_get_tuple_id(stmt->domain);
    amap = isl_map_set_tuple_id(amap, isl_dim_in, st_id);
    
    isl_union_map_dump(build->executed);       
    isl_union_map * umap = isl_union_map_apply_range(isl_union_map_copy(build->executed), isl_union_map_from_map(isl_map_copy(amap)));
    isl_union_map_dump(umap);

    printf("umap_n:%d \n", isl_union_map_n_map(umap));
    assert(isl_union_map_n_map(umap) == 1);

    pth_ast_build_with_isl_ast_expr_list args;
    args.build = build;
    args.scop = scop;
    
    // Append "_flt" for the new array pointer for flattened access
    std::string name(isl_space_get_tuple_name(access_space, isl_dim_out), strlen(isl_space_get_tuple_name(access_space, isl_dim_out)));
    name.append("_flt");    
    access_space = isl_space_set_tuple_name(access_space, isl_dim_out, name.c_str());

    args.tuple_id = isl_space_get_tuple_id(access_space, isl_dim_out);
                
    int success = isl_union_map_foreach_map(umap, pth_generate_access_map_expr_ast, &args);     
    
    if (success == 0) {
      isl_ast_expr * access_id = isl_ast_expr_from_id(isl_id_copy(args.tuple_id));  
                    
      access = isl_ast_expr_access(access_id, args.indices);
    }
      
  } else { 
          
    /*       
    // here just take a specific value as expression AST !!!!!!!
    isl_set * bs = isl_map_range(isl_map_copy(map));              
    isl_point * point = isl_set_sample_point(bs);    
    isl_val * val = isl_point_get_coordinate_val(point, isl_dim_set, 0);
    access = isl_ast_expr_from_val(val);
                 
    //mprinter = isl_printer_print_map(mprinter, access_info.access);
    //std::cerr << isl_printer_get_str(mprinter) << "\n";
    */

    // Junyi for single variable
    //std::cout<<"access map dim_out name: "<< isl_map_get_dim_name(map, isl_dim_out, 2) <<std::endl;
    //std::cout<<"access map n_param: "<< ( isl_map_n_param(map)) <<std::endl;
    //std::cout<<"access map n_out: "<< ( isl_map_n_out(map)) <<std::endl;
    //std::cout<<"access map n_in: "<< ( isl_map_n_in(map)) << "\n" <<std::endl;
    
    //isl_map_dump(map);

    // align tuple id
    isl_id * st_id = isl_set_get_tuple_id(stmt->domain);
    map = isl_map_set_tuple_id(map, isl_dim_in, st_id);
    
    // apply loop range to current map by union_map_apply_range
    isl_union_map * umap = isl_union_map_apply_range(isl_union_map_copy(build->executed), isl_union_map_from_map(isl_map_copy(map)));
    isl_union_map_dump(umap);
    
    isl_map * vmap = isl_map_from_union_map(umap);
    isl_map_dump(vmap);

    // extract piece-wise multi affine expression of the map input
    // only this way?!!!!!!!!!!!!!!!!!!!!
    isl_pw_multi_aff * pwma = isl_pw_multi_aff_from_map(vmap);
    //std::cout<< "pw_multi_aff dim: "<< isl_pw_multi_aff_dim(pwma, isl_dim_out)<< std::endl;
    
    // generate ast exprssion list
    pth_ast_build_with_isl_ast_expr_list args;
    args.build = build;
    args.scop = scop;
    int success = isl_pw_multi_aff_foreach_piece(pwma, pth_generate_v_ast, &args);
    
    // check ast exprssion list number
    //int list_n = isl_ast_expr_list_n_ast_expr(args.indices);
    //std::cout<< "list_n: "<< list_n << std::endl;
    
    // take 1st ast experission
    access = isl_ast_expr_list_get_ast_expr(args.indices, 0);
    //isl_ast_expr_dump(access);

  }
  
  isl_ast_expr_dump(access);
  //assert(false);
  return access;
}



/*
 
    
  
   
    
  if (has_tuple_id) {
     
  isl_aff * aff = pth_flatten_expr_access(scop->scop,  map,  isl_space_get_tuple_id(access_space, isl_dim_out));
        
  isl_map * amap = isl_map_from_pw_aff(isl_pw_aff_from_aff(aff));
   
  amap = isl_map_apply_range(map, amap);
  isl_id * memory_space_id = pth_memory_space_id();
  amap =  isl_map_set_tuple_id(amap, isl_dim_out, isl_id_copy(memory_space_id) );  

  isl_pw_multi_aff * pwma = isl_pw_multi_aff_from_map(amap);
        
  pth_ast_build_with_isl_ast_expr_list args;
  args.build = build;
 
  int success = isl_pw_multi_aff_foreach_piece(pwma, pth_generate_access_expr_ast, &args);
   
  if (success == 0) {   
  isl_ast_expr * access_id = isl_ast_expr_from_id(isl_id_copy(pth_memory_space_id()));
             
  isl_ast_expr * access = isl_ast_expr_access(access_id, args.indices);
  return access;
  //return (pth_ast_expr *)(access);
  }
  * 
  * 
  */
//   isl_printer * mprinter = isl_printer_to_str(ctx);
//  mprinter = isl_printer_set_output_format(mprinter, ISL_FORMAT_C);
//  return pth_ast_expr_from_isl_ast_expr(access);
//  isl_printer_print_ast_expr(mprinter, access);
//std::cerr << "Access Expression " << isl_printer_get_str(mprinter) << std::endl;
 

// }

////////////////////////////////////////////
// The following 2 functions are used for scanning valid iterator positions
////////////////////////////////////////////
// int detect_src_id_aff(isl_set *set, isl_aff *aff, void *user){
  
//   id_record * args = (id_record *)(user);

//   //std::cout<< "aff div number: " << isl_aff_dim(aff, isl_dim_div) <<std::endl;
//   isl_aff_dump(aff);

//   int D = isl_aff_dim(aff, isl_dim_in);
//   isl_val * v;

//   for(int i=0 ; i<D; i++){
//     v = isl_aff_get_coefficient_val(aff, isl_dim_in, i);
    
//     // record non-zero dims
//     if(isl_val_is_zero(v) == 0){      
//       args->src[args->n] = i;
//       args->n = args->n+1;
//       std::cout<< "recording src pos: " << i <<std::endl;
//     }
//     isl_val_free(v);
//   }

//   return 0; 
// }

// int detect_src_id_map(isl_map *map, void *user){

//   id_record * args = (id_record *)(user);
  
//   // take out pw multi affine
//   isl_pw_multi_aff * pwma = isl_pw_multi_aff_from_map(isl_map_copy(map));
//   isl_pw_multi_aff_dump(pwma);
  
//   // take out all pw affine
//   //std::cout<< "pwma dim out number: " <<isl_pw_multi_aff_dim(pwma, isl_dim_out) << std::endl;
//   int n_out = isl_pw_multi_aff_dim(pwma, isl_dim_out);
//   for(int i=0; i<n_out; i++){
//     isl_pw_aff * pwa = isl_pw_multi_aff_get_pw_aff(pwma, i);
//     isl_pw_aff_dump(pwa);    

//     // explore the pw affine
//     isl_pw_aff_foreach_piece(pwa, detect_src_id_aff, args);    
//   }  
  
//   return 0;
// }
