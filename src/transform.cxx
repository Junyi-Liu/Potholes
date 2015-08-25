#include <potholes/transform.h>
#include <potholes/affine.h>

#include <string>
#include <iostream>
#include <fstream>
#include <sstream>

#include </Users/Junyi/research/HLS/pet/expr.h>
#include </Users/Junyi/research/HLS/pet/scop.h>
#include </Users/Junyi/research/HLS/pet/tree.h>
#include </Users/Junyi/research/HLS/pet/loc.h>

#include <isl/ilp.h>
#include <isl/flow.h>
#include <isl/constraint.h>

#include <cassert>

// tansformation constructor
potholes::Transform::Transform(Analysis& analysis) :analysis(analysis) {
              
}

// Memory access scan for pattern details
int acc_expr_scan(pet_expr *expr, void *user){

  stmt_info *info = (stmt_info *) (user);     
  
  // wrapped access checked at first
  // skip non-array access
  isl_map * map = pet_expr_access_get_access(expr);  
  if(isl_map_has_tuple_name(map, isl_dim_out) == 0){
    isl_map_free(map);
    std::cout << "###skip non-array access" << std::endl;
    return 0;
  }

  // assume just 1 target array access   
  isl_pw_aff * pwaff = isl_multi_pw_aff_get_pw_aff(expr->acc.index, 0);

  // Skip scalar write access
  if((pet_expr_access_is_write(expr) == 1) && (pwaff == NULL)){
    std::cout << "### skip analyzing scalar write access" << std::endl;
    // isl_multi_pw_aff_dump(expr->acc.index);
    isl_map_free(map);
    return 0;
  }

  // set up array access info pointer for write and read
  acc_info * acc;
  if(pet_expr_access_is_write(expr)){
    acc = &(info->acc_wr[info->n_acc_wr]);
    info->n_acc_wr = info->n_acc_wr +1;
  }else {
    if(pet_expr_access_is_read(expr) == 0){
      std::cerr<<"unknown access type"<<std::endl;
      isl_map_free(map);
      return -1;
    }
    acc = &(info->acc_rd[info->n_acc_rd]);    
    info->n_acc_rd = info->n_acc_rd +1;
  }

  //record statement index
  acc->idx_stmt = info->idx;

  //record array name
  acc->name = isl_map_get_tuple_name(map, isl_dim_out);
  //std::cout << "acc_tuple_name: "<< acc->name << std::endl;

  //record array access map
  acc->map = isl_map_copy(map);
  isl_map_dump(acc->map);

  //record number of pt and it
  acc->n_pt = isl_map_n_param(map);
  acc->n_it = isl_map_n_in(map);
  
  //record access affine details
  //int success = isl_pw_aff_foreach_piece(pwaff, aff_scan, acc);
  
  isl_map_free(map);
  isl_pw_aff_free(pwaff);
  return 0;
}

// Memory access info for counting
int acc_expr_info(pet_expr *expr, void *user){
  
  stmt_info *info = (stmt_info *) (user);
  
  if(expr->n_arg != 0){
    pet_expr_dump(expr);
    std::cout << "### Number of wrapped accesses "<< expr->n_arg << std::endl;
    std::cout << "### Cannot analyze wrapped access" << std::endl;
    return -1;
  }

  isl_map * map = pet_expr_access_get_access(expr);

  if(isl_map_has_tuple_name(map, isl_dim_out) == 0){
    //isl_map_dump(map);
    isl_map_free(map);
    std::cout << "###skip non-array access" << std::endl;
    return 0;
  }
  
  // assume just 1 target array access   
  isl_pw_aff * pwaff = isl_multi_pw_aff_get_pw_aff(expr->acc.index, 0);

  // Skip scalar write access
  if((pet_expr_access_is_write(expr) == 1) && (pwaff == NULL)){
    std::cout << "### skip analyzing scalar write access" << std::endl;
    // isl_multi_pw_aff_dump(expr->acc.index);
    isl_map_free(map);
    return 0;
  }

  info->n_pt = isl_map_n_param(map);
  info->n_it = isl_map_n_in(map);
  
  // record number of accesses for write and read
  if(pet_expr_access_is_write(expr)){
    info->n_acc_wr = info->n_acc_wr +1;
  }else if(pet_expr_access_is_read(expr)){
    info->n_acc_rd = info->n_acc_rd +1;
  }

  isl_map_free(map);
  isl_pw_aff_free(pwaff);
  return 0;
}

// isl_access_level_before func for dependency analysis
int acc_order(void * first, void * second){

  acc_info * acc_1 = (acc_info *)first;
  
  // on the same line, write is always after read
  return 2*(acc_1->n_it);
}

// get affine+1 for get_dim_size
// int get_aff_plus_1(__isl_take isl_set * set, __isl_take isl_aff * aff, void * user ){

//   isl_aff ** dist_aff = (isl_aff **)user;
  
//   if( *dist_aff == NULL ){
//     *dist_aff = isl_aff_copy(aff);
//     isl_aff_dump(*dist_aff);
//   }

//   isl_aff_free(aff);
//   isl_set_free(set);
//   return 0;
// }

// Extract lower & upper bounds in isl_aff 
//int extract_dim_bound(__isl_take isl_constraint * c, void * user){
int extract_dim_bound(__isl_take isl_constraint * lw, __isl_take isl_constraint * up, __isl_take isl_basic_set * bset, void * user){
  bd_info * bd = (bd_info *) user;
  //isl_constraint_dump(c);
  
  std::cout <<"-- lower bd: " << std::endl; 
  bd->min = isl_constraint_get_bound(lw, isl_dim_set, bd->dim);
  isl_aff_dump(bd->min);
  std::cout <<"-- upper bd: " << std::endl; 
  bd->max = isl_constraint_get_bound(up, isl_dim_set, bd->dim);
  isl_aff_dump(bd->max);
  
  isl_constraint_free(lw);
  isl_constraint_free(up);
  isl_basic_set_free(bset);
  return 0;
}

// Scan bset for lower & upper bounds
int scan_bset_for_bd(__isl_take isl_basic_set *bset, void *user){

  bd_info * bd = (bd_info *) user;

  //not handle bset number>1
  //int s1 = isl_basic_set_foreach_constraint(bset, extract_dim_bound, bd);
  int s1 = isl_basic_set_foreach_bound_pair(bset, isl_dim_set, bd->dim, extract_dim_bound, bd);
  
  isl_basic_set_free(bset);
  return 0;
}

// Get the size of the dimention of a given isl_set
isl_aff * get_dim_size(__isl_keep isl_set * set, unsigned dim){

  isl_set_dump(set);
  
  // isl_pw_aff * max_pwaff = isl_set_dim_max(isl_set_copy(set), dim);
  // isl_pw_aff * min_pwaff = isl_set_dim_min(isl_set_copy(set), dim);
  // isl_pw_aff_dump(max_pwaff);
  // isl_pw_aff_dump(min_pwaff);
  
  // isl_pw_aff * dist_pwaff = isl_pw_aff_sub(max_pwaff, min_pwaff);
  // isl_pw_aff_dump(dist_pwaff);

  // assert(false);
  
  // isl_aff * dist_aff = NULL;  
  // int success = isl_pw_aff_foreach_piece(dist_pwaff, get_aff_plus_1, &dist_aff);
  // isl_aff_dump(dist_aff);

  // isl_space * sp = isl_set_get_space(set);
  // isl_aff * rtn_aff = isl_aff_zero_on_domain(isl_local_space_from_space(sp));
  
  // // copy distance affine to the proper domain space
  // rtn_aff = isl_aff_set_constant_val(rtn_aff, isl_aff_get_constant_val(dist_aff));
  // for(int i = 0; i< isl_aff_dim(rtn_aff, isl_dim_param); i++){
  //   rtn_aff = isl_aff_set_coefficient_val(rtn_aff, isl_dim_param, i, isl_aff_get_coefficient_val(dist_aff, isl_dim_param, i));
  // }
  // isl_aff_dump(rtn_aff);

  // //isl_pw_aff_free(dist_pwaff);
  // isl_aff_free(dist_aff);
  // return isl_aff_add_constant_si(rtn_aff, 1); //max-min+1
  
  bd_info bd;
  bd.dim = dim;
  int s1 = isl_set_foreach_basic_set(set, scan_bset_for_bd, &bd);

  isl_aff * dist_aff = isl_aff_sub(bd.max, bd.min);
  isl_aff_dump(dist_aff);
  //assert(false);
  
  return isl_aff_add_constant_si(dist_aff, 1); //max-min+1
}

// check multi-affine difference
int check_multi_aff_diff(isl_set * set, isl_multi_aff * maff, void * user){

  stmt_info * stmt = (stmt_info *)user;

  std::cout << "=== current piece set: "<< std::endl;
  isl_set_dump(set);
  //assert(false);

  int d_maff = isl_multi_aff_dim(maff, isl_dim_out);

  d_maff = (stmt->n_it < d_maff) ? stmt->n_it : d_maff;
  
  // (src-snk) in multi-afffine
  for(int i=0; i<d_maff; i++){
    isl_aff * snk_aff = isl_multi_aff_get_aff(maff, i);
    isl_aff * src_aff = isl_aff_list_get_aff(stmt->src, i);
    //isl_aff_dump(snk_aff);
    snk_aff = isl_aff_sub(src_aff, snk_aff);
    maff = isl_multi_aff_set_aff(maff, i, snk_aff);
  }
  std::cout << "* original (src-snk): "<< std::endl;
  isl_multi_aff_dump(maff);

  //assert(false);

  // flatten (src-snk)
  std::cout << "** Flattening for (src-snk)" << std::endl;
  int outer_dep = 0;
  int dep_pos = stmt->n_it-1;
  isl_set * dom_no_divs = isl_set_remove_divs(isl_set_copy(stmt->domain));
  isl_space * sp = isl_multi_aff_get_domain_space(maff);
  isl_local_space * lsp = isl_local_space_from_space(sp);
  isl_ctx * ctx = isl_local_space_get_ctx(lsp);
  isl_val * val_one = isl_val_one(ctx);
  isl_aff * ftr = isl_aff_val_on_domain(isl_local_space_copy(lsp), val_one);
  isl_aff * diff = isl_aff_zero_on_domain(isl_local_space_copy(lsp));
  for(int i=stmt->n_it-1; i>=0; i--){
    std::cout << "* dimension: "<< i << std::endl;

    // add dimension item with factor
    if(i < d_maff){
      // take current dimension difference(distance)
      isl_aff * dim = isl_multi_aff_get_aff(maff, i);

      // check whether dependency is at the outer dimension
      if(i < stmt->n_it-1){
	isl_constraint * dim_cst = isl_equality_from_aff(isl_aff_copy(dim));
	isl_set * dim_set = isl_set_from_basic_set(isl_basic_set_from_constraint(dim_cst));
	dim_set = isl_set_intersect(isl_set_copy(set), dim_set);
	if(isl_set_is_empty(dim_set) == 1){
	  if(i < dep_pos) dep_pos = i;
	  outer_dep = 1;
	  std::cout << "Outer dependency is found " << std::endl;
	}
	isl_set_free(dim_set);
      }

      // multiply with the size of previous dimensions 
      dim = isl_aff_mul(dim, isl_aff_copy(ftr));

      // add to the final difference(distance)
      diff = isl_aff_add(diff, dim);
    }
    
    // scale up factor
    // consider paramterized dim bounds
    if(i>0){
      ftr = isl_aff_mul(ftr, get_dim_size(dom_no_divs, i));
      isl_aff_dump(ftr);
    }
  }
  isl_set_free(dom_no_divs);


  // check diff availability
  if(diff){  
    std::cout << "* flattened (src-snk): "<< std::endl;
    isl_aff_dump(diff);
    isl_aff_free(ftr);  
    //isl_ctx_free(ctx);
  }
  else{
    std::cout << "\n** Cannot flatten (src-snk), mainly due to the multiplication of iterators or parameters in affine expression  \n"<< std::endl;
    assert(false);
  }
  
  // src-snk + L-1 >=0
  std::cout << "** Creating: src-snk + L-1 >=0" << std::endl;
  isl_constraint * cst = isl_inequality_from_aff(isl_aff_copy(diff)); 
  // constant += L-1, L is delay cycles, which is >=1 !!!!!!!!!!!!!!!!
  isl_val * c_val = isl_constraint_get_constant_val(cst);
  int c_num = isl_val_get_num_si(c_val);
  isl_val_free(c_val);
  cst = isl_constraint_set_constant_si(cst, c_num + stmt->L_delay -1 );
  isl_constraint_dump(cst);
  isl_set * cst_ub = isl_set_from_basic_set(isl_basic_set_from_constraint(cst));

  // snk-src -1 >=0
  // affine: sink-source = distance
  std::cout << "** Creating: snk-src-1 >= 0" << std::endl;
  diff = isl_aff_sub(isl_aff_zero_on_domain(isl_local_space_copy(lsp)), diff); //0 - (src-snk)
  cst = isl_inequality_from_aff(isl_aff_copy(diff));
  // constant += -1
  c_val = isl_constraint_get_constant_val(cst);
  c_num = isl_val_get_num_si(c_val);
  isl_val_free(c_val);
  cst = isl_constraint_set_constant_si(cst, c_num -1 );
  isl_constraint_dump(cst);  
  isl_set * cst_lb = isl_set_from_basic_set(isl_basic_set_from_constraint(cst));    

  // intersect lower and upper bounds
  std::cout << "** Intersecting lower&upper bounds" << std::endl;
  isl_set * bd = isl_set_intersect(cst_lb, cst_ub);
  isl_set_dump(bd);
  
  // intersect scop domain
  //bd = isl_set_intersect(isl_set_copy(stmt->domain), bd);
  //isl_set_dump(bd);
  
  // intersect current piece set !!!!!!!!!!
  std::cout << "** Intersecting current piece "<< std::endl;
  bd = isl_set_intersect(set,bd);
  isl_set_dump(bd);
  
  //isl_set_dump(stmt->context);
  //assert(false);

  // ** check emptiness for whether further check parameters
  std::cout << "** Analyzing emptiness" << std::endl;
  isl_set * empty;
  if(isl_set_is_empty(bd)){
    // when bd is already empty
    empty = isl_set_universe(isl_set_get_space(stmt->context));
    isl_set_dump(empty);
  }
  else{
    // when bd is determined to be empty
    //bd = isl_set_partial_lexmax(bd, isl_set_copy(stmt->context), &empty);  // consider parameter context from scop
    isl_set * pnt_lex = isl_set_partial_lexmax(isl_set_copy(bd), isl_set_universe(isl_set_get_space(stmt->context)), &empty);  // start from universal set
    
    isl_set_dump(pnt_lex);
    isl_set_dump(empty);
    
    isl_set_free(pnt_lex);
    //assert(false);
  }

  // Add results
  // remove statement id for stmt->cft
  // when statement schedule dimension numbers are different
  bd = isl_set_reset_tuple_id(bd);
  std::cout << "** Adding result" << std::endl;
  if(isl_set_is_empty(bd) != 1){
    // set_intersect for difference pieces(conditions), since current piece's safe range contains other piece's conflict range
    stmt->param = isl_set_intersect(stmt->param,isl_set_copy(empty));
    stmt->cft = isl_set_union(stmt->cft, isl_set_copy(bd));    
    if(outer_dep == 0) stmt->outer_dep = 0;

    // store flattened dependence distance in pw_aff with conflict region
    /*
    isl_pw_aff * dist = isl_pw_aff_from_aff(isl_aff_copy(diff));
    dist = isl_pw_aff_reset_tuple_id(dist, isl_dim_in);
    //dist = isl_pw_aff_intersect_domain(dist, isl_set_copy(bd));
    dist = isl_pw_aff_intersect_params(dist, isl_set_complement(isl_set_copy(empty)) );
    if(stmt->dist){
      stmt->dist = isl_pw_aff_union_min(stmt->dist, dist);
    }
    else{
      stmt->dist = isl_pw_aff_copy(dist);
    }
    // isl_pw_aff_dump(dist);
    */


    // store innermost conflict dependence distance in pw_aff with conflict region
    std::cout << "Current inner conflict dep pos:  " << dep_pos << std::endl;
    isl_aff * dist_aff = isl_multi_aff_get_aff(maff, dep_pos);
    dist_aff = isl_aff_sub(isl_aff_zero_on_domain(isl_local_space_copy(lsp)), dist_aff); // 0-(src-snk)
    isl_pw_aff * dist = isl_pw_aff_from_aff(dist_aff);
    dist = isl_pw_aff_reset_tuple_id(dist, isl_dim_in);
    dist = isl_pw_aff_intersect_params(dist, isl_set_complement(isl_set_copy(empty)));
    
    if(stmt->dep_pos == -1){
      // first record
      stmt->dep_pos = dep_pos;
      stmt->dist = isl_pw_aff_copy(dist);
    }
    else if(stmt->dep_pos == dep_pos){
      // take min distance
      stmt->dist = isl_pw_aff_union_min(stmt->dist, isl_pw_aff_copy(dist));      
    }
    else if(stmt->dep_pos < dep_pos){
      // found inner dep pos, discard previous record
      stmt->dep_pos = dep_pos;
      isl_pw_aff_free(stmt->dist);
      stmt->dist = isl_pw_aff_copy(dist);      
    }        
    isl_pw_aff_free(dist);
    
  }

  //assert(false);

  std::cout << "** param set : " << std::endl;
  isl_set_dump(stmt->param);

  std::cout << "** dep distance : " << std::endl;
  isl_pw_aff_dump(stmt->dist);
  //assert(false);

  isl_local_space_free(lsp);
  isl_multi_aff_free(maff);
  isl_aff_free(diff);
  isl_set_free(empty);
  isl_set_free(bd);
  //isl_set_free(set);
  return 0;
}

// Dependency analysis Func for multi-D access
int dep_analysis(isl_map * dep, int must, void * dep_user, void * user){
  
  //acc_info * acc_wr = (acc_info *)dep_user;
  stmt_info * stmt = (stmt_info *)user;

  std::cout << "=== Start dependency flow analysis" << std::endl;
  std::cout << "=== current dep map:" << std::endl;
  isl_map_dump(dep);

  //assert(false);
  
  // Apply stmt->domain onto both dep domain and range !!!!!
  // std::cout << "=== Apply src bounds" << std::endl;
  // dep = isl_map_intersect_domain(dep, isl_set_copy(stmt->domain));
  // isl_map_dump(dep);
  // std::cout << "=== Apply snk bounds" << std::endl;
  // dep = isl_map_intersect_range(dep, isl_set_copy(stmt->dom_snk));
  // isl_map_dump(dep);
  // //assert(false);

  //dep = isl_map_coalesce(dep);
  
  // take lexmin for the case that map is not single-valued !!!!!!!
  std::cout << "=== Taking Lexmin sink" << std::endl;
  dep = isl_map_lexmin(dep);
  isl_map_dump(dep);  
  
  // sink affine
  std::cout << "=== Extract affine" << std::endl;
  isl_pw_multi_aff * snk = isl_pw_multi_aff_from_map(isl_map_copy(dep));
  //isl_pw_aff * snk = isl_pw_multi_aff_get_pw_aff(pwm_aff, 0);
  isl_pw_multi_aff_dump(snk);
  //isl_pw_multi_aff_free(pwm_aff);
  
  
  // statement domain
  //isl_set_dump(stmt->domain);
    
  // source affine
  //isl_space * sp = isl_set_get_space(isl_set_copy(stmt->domain));
  isl_space * sp = isl_set_get_space(isl_map_domain(dep));
  isl_local_space * lsp = isl_local_space_from_space(sp);
  stmt->src = isl_aff_list_alloc(isl_local_space_get_ctx(lsp), 0);
  for(int i = 0; i< isl_local_space_dim(lsp, isl_dim_set); i++){
    stmt->src = isl_aff_list_add(stmt->src, isl_aff_var_on_domain(isl_local_space_copy(lsp), isl_dim_set, i));
  }
  isl_local_space_free(lsp);
  isl_aff_list_dump(stmt->src);

  //assert(false);

  // source affine
  // isl_space * sp = isl_set_get_space(isl_set_copy(stmt->domain));
  // isl_local_space * lsp = isl_local_space_from_space(sp);
  // stmt->src = isl_aff_var_on_domain(lsp, isl_dim_set, 0);
  // isl_aff_dump(stmt->src);

  // distance between source and sink
  std::cout << "=== Analyze dependency distance" << std::endl;
  int success = isl_pw_multi_aff_foreach_piece(snk, check_multi_aff_diff, stmt);
  
  std::cout << "=== Finish dependency flow analysis" << std::endl;

  //isl_set_dump(stmt->param);
  isl_pw_multi_aff_free(snk);
  isl_aff_list_free(stmt->src);
  return 0;

}


/*
 * User defined Scop Analysis
 */  
void analyzeScop(pet_scop * scop, VarMap * vm, VarMap * tm, recur_info * rlt){

  std::cout << "###########" << std::endl; 
  pet_scop_dump(scop);
  std::cout << "###########" << std::endl;

  // Record array access name and type
  for (int j = 0 ; j < scop->n_array  ; j++ ) {
    std::string element_type = scop->arrays[j]->element_type;    
    std::string pname = isl_set_get_tuple_name(scop->arrays[j]->extent);   
    std::string ptype = element_type + std::string("*");   
    vm->insert(std::pair<std::string, std::string>(pname, ptype));

    //isl_set_dump(scop->arrays[j]->extent);
    //std::cout << "dim_in: " << isl_set_dim(scop->arrays[j]->extent, isl_dim_set) << std::endl;
    if(isl_set_dim(scop->arrays[j]->extent, isl_dim_set) > 0){
      tm->insert(std::pair<std::string, std::string>(pname, " "));      
    }
    else{
      tm->insert(std::pair<std::string, std::string>(pname, " &")); 
    }      
    
  }
  //assert(false);
  
  // Statements info
  // Scan all statments
  if(isl_set_is_empty(scop->stmts[0]->domain)){
    std::cout << "Empty Scop Domain, Check the correctness of the original code" << std::endl;   
    assert(false);
  }
  int n_stmt = scop->n_stmt;
  std::cout << "*** Number of statments in the loop: "<< n_stmt << std::endl; 
  stmt_info stmt;
  stmt.scop = scop;  
  stmt.context = isl_set_copy(scop->context);
  stmt.param = NULL;

  // Counting the number of Rd & Wr array accesses respectively 
  for(int i = 0; i<n_stmt; i++){
    int s1 = pet_tree_foreach_access_expr(scop->stmts[i]->body, acc_expr_info, &stmt);  
    if (s1 == -1){
      isl_set_free(stmt.context);
      return;
    }
  }
  //assert(false);
  
  // isl_map_dump(scop->stmts[0]->schedule);

  // Set up write containers
  acc_info acc_wr[stmt.n_acc_wr];
  stmt.acc_wr = acc_wr;
  // int pt_coeff_wr[stmt.n_acc_wr][stmt.n_pt];
  // int it_coeff_wr[stmt.n_acc_wr][stmt.n_it];
  // for(int i=0; i<stmt.n_acc_wr; i++){
  //   acc_wr[i].pt_coeff = &pt_coeff_wr[i][0];
  //   acc_wr[i].it_coeff = &it_coeff_wr[i][0];    
  // }  

  // Set up read containers
  acc_info acc_rd[stmt.n_acc_rd];
  stmt.acc_rd = acc_rd;
  // int pt_coeff_rd[stmt.n_acc_rd][stmt.n_pt];
  // int it_coeff_rd[stmt.n_acc_rd][stmt.n_it];
  // for(int i=0; i<stmt.n_acc_rd; i++){
  //   acc_rd[i].pt_coeff = &pt_coeff_rd[i][0];
  //   acc_rd[i].it_coeff = &it_coeff_rd[i][0];
  // }  

 
  // Scan detail access patterns
  stmt.n_acc_wr = 0;
  stmt.n_acc_rd = 0;
  for(int i = 0; i<n_stmt; i++){
    stmt.idx = i;
    int s2 = pet_tree_foreach_access_expr(scop->stmts[i]->body, acc_expr_scan, &stmt);
    if (s2 == -1){
      isl_set_free(stmt.context);
      return;
    } 
  }

  // Propose best initial interval considering 2 port per memory
  // just consider the array with write access !!!!!!!
  int mem_port = 1;
  for(int j=0; j<stmt.n_acc_wr; j++){
    int tmp_port = 1;
    for(int i=0; i<stmt.n_acc_rd; i++){
      // only count read access with same name of write access
      if(strcmp(acc_rd[i].name, acc_wr[j].name) == 0){
	tmp_port = tmp_port + 1; 
      }
    }
    if(tmp_port > mem_port){
      mem_port = tmp_port;
    }
  }
  std::cout<< "*** required memory port: " << mem_port << std::endl;
  stmt.II = ceil(float(mem_port)/2);
  std::cout<< "*** proposed best II: " << stmt.II << std::endl;

  // Read data file for statement delay infomation
  std::string line;
  std::ifstream datfile (delay_info_path);
  if(datfile.is_open()){
    getline(datfile, line);
    std::cout<< "*** Reading info " << std::endl;
    datfile.close();
  }
  else{
    std::cout<< "*** Cannot read daley info file" << line << std::endl;
    assert(false);
  }
  std::istringstream (line) >> stmt.L_delay;
  std::cout<< "*** Delay info: " << stmt.L_delay << std::endl;
  rlt->delay = stmt.L_delay;
  // assume that delay will not increase over 1.2 times
  stmt.L_delay = ceil(float(stmt.L_delay)*1.2/float(stmt.II));
  std::cout<< "*** Ceil( Delay/II * 1.2 ): " << stmt.L_delay << std::endl;  

  // Make domain always non-empty
  // std::cout << "** Checking domain emptiness " << std::endl; 
  // stmt.domain = isl_set_copy(scop->stmts[0]->domain);
  // isl_set * empty;
  // isl_set * dom_lexmax = isl_set_partial_lexmax(isl_set_copy(stmt.domain), isl_set_universe(isl_set_get_space(stmt.context)), &empty);  // start from universal set
  // if(isl_set_is_empty(empty) != 1){
  //   std::cout << "** exist paramter constraints for empty domain" << std::endl;  
  //   isl_set_dump(empty);
  //   //empty = isl_set_complement(empty);
  //   //isl_set_dump(empty);
  //   // add constraints of non-empty domain
  //   //stmt.param = isl_set_copy(empty);
  // }
  // isl_set_free(dom_lexmax);
  // isl_set_free(empty);  
  //assert(false);

  // Analyze parameter range
  std::cout << "***************** SCOP ANALYSIS START *******************" << std::endl;

  // safe region start from universe set
  stmt.param = isl_set_universe(isl_set_get_space(stmt.context));
  // conflict region start from empty set
  stmt.cft = isl_set_empty(isl_set_get_space(stmt.context));
  
  // S/M-Wr S/M-Rd
  // Current: consider all Wr-Rd access pairs with same array name !!!!!!!!!
  isl_access_info * access;
  isl_flow * flow;
  int s3;
  for(int j = 0; j<stmt.n_acc_wr; j++){
    std::cout << "======= Start write access: "<< j << "========"<< std::endl;
    
    // assign corresponding write access domain
    stmt.domain = isl_set_copy(scop->stmts[acc_wr[j].idx_stmt]->domain);
    //isl_set_dump(stmt.domain);
    if(isl_set_is_wrapping(stmt.domain)){
      stmt.domain = isl_map_domain(isl_set_unwrap(stmt.domain));
      //isl_set_dump(stmt.domain);
      //assert(false);      
    }

    std::cout << "==== Schedule: " << std::endl;
    isl_map_dump(scop->stmts[acc_wr[j].idx_stmt]->schedule);

    // record number of pt and it
    stmt.n_pt = isl_set_n_param(stmt.domain);
    stmt.n_it = isl_set_n_dim(stmt.domain);
    
    // analyze Wr-Rd pairs
    for(int i=0; i<stmt.n_acc_rd; i++){
      // check name, only analysis array access with same name !!!!!!!
      if(strcmp(acc_rd[i].name, acc_wr[j].name) != 0){
	continue;
      }
      std::cout << "***read access: "<< i << std::endl;

      // assign corresponding read access domain
      stmt.dom_snk = isl_set_copy(scop->stmts[acc_rd[i].idx_stmt]->domain);
      if(isl_set_is_wrapping(stmt.dom_snk)){
	stmt.dom_snk = isl_map_domain(isl_set_unwrap(stmt.dom_snk));
	//isl_set_dump(stmt.dom_snk);
	//assert(false);      
      }
      
      // record which read access
      stmt.rd_pos = i;

      // Apply statement domains onto both src and snk map !!!!!
      std::cout << "=== Apply src bounds" << std::endl;
      isl_map * src_map = isl_map_intersect_domain(isl_map_copy(acc_wr[j].map), isl_set_copy(stmt.domain));
      isl_map_dump(src_map);
      std::cout << "=== Apply snk bounds" << std::endl;
      isl_map * snk_map = isl_map_intersect_domain(isl_map_copy(acc_rd[i].map), isl_set_copy(stmt.dom_snk));
      isl_map_dump(snk_map);
      
      //assert(false);
      
      // create access info for one read access (sink)
      access = isl_access_info_alloc(snk_map, &(acc_rd[i]), acc_order, 1);
      // add write access (source)
      access = isl_access_info_add_source(access, src_map, 1, &(acc_wr[j]));

      // compute flow
      std::cout << "** start computing flow" << std::endl;
      flow = isl_access_info_compute_flow(access); 
      std::cout << "** finish computing flow" << std::endl;
      
      // analyze flow
      s3 = isl_flow_foreach(flow, dep_analysis, &stmt);
    
      // check whether there is no_source relation
      // isl_map * no_src = isl_flow_get_no_source(flow, 1);
      // if(isl_map_is_empty(no_src) !=1){
      // 	if(stmt.param == NULL){
      // 	  stmt.param = isl_set_universe(isl_set_get_space(stmt.context));
      // 	}
      // 	else{
      // 	  stmt.param = isl_set_intersect(stmt.param, isl_set_universe(isl_set_get_space(stmt.context)));
      // 	}
      // }
      // isl_map_free(no_src);
    
      // free isl_flow
      isl_flow_free(flow);
      // free current snk domain
      isl_set_free(stmt.dom_snk);
      std::cout << "*** " << s3 <<std::endl;
    }

    // free current write access domain
    isl_set_free(stmt.domain);
    
    std::cout << "======= Finish Write access: "<< j << "========"<< std::endl;
  }

  // try to remove the constraints for invalid loop bounds
  // if(isl_set_is_empty(empty) != 1){
  //   std::cout << "** adding paramter constraints for non-empty domain" << std::endl;  
  //   stmt.param = isl_set_intersect(stmt.param, isl_set_complement(isl_set_copy(empty)));
  //   isl_set_dump(stmt.param);
  // }
  // isl_set_free(empty);
  
  // Remove redundancies
  std::cout << "* Remove redundancies of param" << std::endl; 
  stmt.param = isl_set_remove_redundancies(stmt.param);
  isl_set_dump(stmt.param);
  stmt.cft = isl_set_remove_redundancies(stmt.cft);
  
  
  // Coalescing
  std::cout << "* Coalescing param " << std::endl;   
  stmt.param = isl_set_coalesce(stmt.param);
  isl_set_dump(stmt.param);
  stmt.cft = isl_set_coalesce(stmt.cft);
  stmt.dist = isl_pw_aff_coalesce(stmt.dist);
  
  //stmt.param = isl_set_detect_equalities(stmt.param);

  // isl_map * dep_non = isl_flow_get_no_source(flow, 1);
  // isl_map_dump(dep_non);
  std::cout << "***************** SCOP ANALYSIS END *******************" << std::endl; 

  // copy final results
  rlt->param = isl_set_copy(stmt.param);
  rlt->cft = isl_set_copy(stmt.cft);
  rlt->outer_dep = stmt.outer_dep;
  rlt->dist = isl_pw_aff_copy(stmt.dist);

  //assert(false);
  
  // Free isl objects
  for(int i=0; i<stmt.n_acc_wr; i++){
    // clear isl related objects
    isl_map_free(acc_wr[i].map);
    //isl_aff_free(acc_wr[i].aff);    
  }  

  for(int i=0; i<stmt.n_acc_rd; i++){
    // clear isl related object
    isl_map_free(acc_rd[i].map);
    //isl_aff_free(acc_rd[i].aff);
  }
  
  //isl_set_free(stmt.domain);
  isl_set_free(stmt.context);
  //isl_flow_free(flow);
  //isl_set_dump(stmt.param);
  isl_set_free(stmt.param);
  isl_set_free(stmt.cft);
  isl_pw_aff_free(stmt.dist);
  return;

}


// Affine scan
// int aff_scan(isl_set *set, isl_aff *aff, void *user){
  
//   acc_info *info = (acc_info *) (user);  
  
//   // affine
//   //isl_aff_dump(aff);
//   //info->aff = isl_aff_copy(aff); 
 
//   isl_val * v;

//   // parameters
//   int n_dim_p = isl_aff_dim(aff, isl_dim_param);
//   for(int i=0; i<n_dim_p ;i++){
//     v = isl_aff_get_coefficient_val(aff, isl_dim_param, i);
//     //isl_val_dump(v);
//     info->pt_coeff[i] = isl_val_get_num_si(v);
//     isl_val_free(v);
//   }
  
//   // iterators
//   int n_dim_i = isl_aff_dim(aff, isl_dim_in);
//   for(int i=0; i<n_dim_i ;i++){
//     v = isl_aff_get_coefficient_val(aff, isl_dim_in, i);
//     //isl_val_dump(v);
//     info->it_coeff[i] = isl_val_get_num_si(v);
//     isl_val_free(v);    
//   }

//   // constant
//   v = isl_aff_get_constant_val(aff);
//   info->cnt = isl_val_get_num_si(v);
  
//   isl_val_free(v);
//   isl_aff_free(aff);
//   isl_set_free(set);
//   return 0;
// }


int apply_ineq_upper_bound(__isl_take isl_constraint * c, void * user){

  cst_info * info = (cst_info *) (user);  
  
  if(isl_constraint_is_upper_bound(c, isl_dim_set, info->i_dim)){

    if(isl_constraint_is_equality(c) != 1){
      std::cout << "*** Upper bound of inner-most dimension is an inequality constraint " << std::endl;
      isl_constraint_dump(c);

      std::cout << "*** Add new inner most loop upper bound " << std::endl; 
      isl_set * tmp = isl_set_add_constraint(isl_set_copy(info->stmt_dom), isl_constraint_copy(c));

      tmp = isl_set_intersect_params(tmp, isl_set_copy(info->param));
      
      isl_set_dump(tmp);

      std::cout << "*** Current temporary dom " << std::endl;
      isl_set_dump(info->tmp_dom);
      
      std::cout << "*** Combine " << std::endl;       
      info->tmp_dom = isl_set_intersect(tmp, info->tmp_dom); 
      
      isl_set_dump(info->tmp_dom);      

      info->n_cst +=1; 
    }
    
  }

  isl_constraint_free(c);

  return 0;
}

int apply_eq_upper_bound(__isl_take isl_constraint * c, void * user){

  cst_info * info = (cst_info *) (user);  

  // int s = isl_constraint_is_lower_bound(c, isl_dim_set, isl_constraint_dim(isl_constraint_copy(c), isl_dim_set)-1);
  // std::cout << "*** Upper bound: "<< s << std::endl; 

  int s = isl_constraint_involves_dims(c, isl_dim_set, info->i_dim, 1);
  std::cout << "*** Inner-most dimension: "<< s << std::endl; 
  
  if(s){

    if(isl_constraint_is_equality(c) == 1){
      std::cout << "*** Inner-most dimension equality constraint " << std::endl;
      isl_constraint_dump(c);

      // Create new inequality constaint
      std::cout << "*** Point affine " << std::endl; 
      isl_aff * tmp_aff = isl_constraint_get_aff(c);
      isl_aff_dump(tmp_aff);
      std::cout << "*** Create inequality constraint affine" << std::endl;

      // tmp_aff * -1
      isl_space * sp = isl_aff_get_domain_space(tmp_aff);
      isl_local_space * lsp = isl_local_space_from_space(sp);
      isl_aff * factor = isl_aff_zero_on_domain(lsp); //zero
      factor = isl_aff_set_constant_si(factor, -1);
      tmp_aff = isl_aff_mul(tmp_aff, factor);
      
      // inequality for non-negative (>=0)      
      isl_constraint * tmp_cst = isl_inequality_from_aff(tmp_aff);
      isl_constraint_dump(tmp_cst);

      std::cout << "*** Add new inner most loop upper bound " << std::endl; 
      info->tmp_dom = isl_set_add_constraint(info->tmp_dom, tmp_cst);
      info->tmp_dom = isl_set_intersect_params(info->tmp_dom, isl_set_copy(info->param));
      isl_set_dump(info->tmp_dom);

      info->n_cst +=1; 
    }
    
  }

  isl_constraint_free(c);

  return 0;
}

int constraint_scan(__isl_take isl_basic_set * bset, void * user){

  // isl_set * stmt_dom = (isl_set *) (user);
  cst_info * info = (cst_info *) (user);
  
  std::cout << "***** New Basic Set " << std::endl;
  isl_basic_set_dump(bset);
  //std::cout << isl_basic_set_n_constraint(bset) << std::endl;

  // set up constraint info
  info->param = isl_set_from_basic_set(isl_basic_set_params(isl_basic_set_copy(bset)));
  info->n_cst = 0;
  info->tmp_dom = isl_set_copy(info->stmt_dom);

  std::cout << "***** Parameter set " << std::endl;
  isl_set_dump(info->param);

  // take inequality constraints of inner-most dimension as the new upper bound
  // CURRENT approach produces rough split points !!!!!!!!
  int s1 = isl_basic_set_foreach_constraint(bset, apply_ineq_upper_bound, info);
  
  // if no iequality constraints are found, take equality ones as the upper bound
  if(info->n_cst == 0){
    std::cout << "**** No inequality constraints are found " << std::endl;
    s1 = isl_basic_set_foreach_constraint(bset, apply_eq_upper_bound, info); 
  }
  
  // Creat new domian for current basic set
  std::cout << "***** New domain " << std::endl;
  if(info->n_bst == 0){
    info->new_dom = isl_set_copy(info->tmp_dom); 
  }
  else{
    info->new_dom = isl_set_union(isl_set_copy(info->tmp_dom), info->new_dom); 
  }
  info->new_dom = isl_set_remove_redundancies(info->new_dom); 
  info->new_dom = isl_set_coalesce(info->new_dom);
  isl_set_dump(info->new_dom);

  info->n_bst +=1; 
  
  isl_set_free(info->tmp_dom);
  isl_set_free(info->param);
  isl_basic_set_free(bset);
  
  return 0;
}

// Compare lower & upper bounds in isl_aff 
int compare_dim_bound(__isl_take isl_constraint * lw, __isl_take isl_constraint * up, __isl_take isl_basic_set * bset, void * user){
  bd_info * bd = (bd_info *) user;
  //isl_constraint_dump(c);
  
  std::cout <<"-- lower bd: " << std::endl; 
  isl_aff * min = isl_constraint_get_bound(lw, isl_dim_set, bd->dim);
  isl_aff_dump(min);
  std::cout <<"-- upper bd: " << std::endl; 
  isl_aff * max = isl_constraint_get_bound(up, isl_dim_set, bd->dim);
  isl_aff_dump(max);

  bool eq_max = isl_aff_plain_is_equal(bd->max, max);
  bool eq_min = isl_aff_plain_is_equal(bd->min, min);  

  isl_aff_free(max);
  isl_aff_free(min);
  isl_constraint_free(lw);
  isl_constraint_free(up);
  isl_basic_set_free(bset);
  
  if(eq_max && eq_min){
    return 0;
  }
  else{
    return -1;
  }
}
// Scan bset for lower & upper bounds
int scan_bset_cmp_bd(__isl_take isl_basic_set *bset, void *user){

  bd_info * bd = (bd_info *) user;

  //not handle bset number>1
  int s1 = isl_basic_set_foreach_bound_pair(bset, isl_dim_set, bd->dim, compare_dim_bound, bd);
  
  isl_basic_set_free(bset);
  return s1;
}
// Compare dimension size of two input sets
int compare_dim_size(__isl_keep isl_set * dom, __isl_keep isl_set * cft, unsigned dim){

  std::cout <<"** stmt dom: " << std::endl; 
  isl_set_dump(dom);
  std::cout <<"** cft set: " << std::endl; 
  isl_set_dump(cft);
  
  bd_info bd;
  bd.dim = dim;
  // scan dom set
  int s1 = isl_set_foreach_basic_set(dom, scan_bset_for_bd, &bd);
  // scan cft set to compare with dom
  s1 = isl_set_foreach_basic_set(cft, scan_bset_cmp_bd, &bd);

  isl_aff_free(bd.max);
  isl_aff_free(bd.min);
  //assert(false);

  //s1=0: equal, s1=-1: inequal
  return s1+1; 
}


// compare bound pair
// problem: if there is eq_cst on dim, other ineq_cst will be neglected
int cmp_bound_pair(__isl_take isl_constraint * lw, __isl_take isl_constraint * up, __isl_take isl_basic_set * bset, void * user){

  bd_info * bd = (bd_info *) user;
  //std::cout <<"-- lower bd: " << std::endl; 
  bd->min = isl_constraint_get_bound(lw, isl_dim_set, bd->dim);
  //isl_aff_dump(bd->min);
  //std::cout <<"-- upper bd: " << std::endl; 
  bd->max = isl_constraint_get_bound(up, isl_dim_set, bd->dim);
  //isl_aff_dump(bd->max);

  // stop scan when bounds are not equal
  bool ds = isl_aff_plain_is_equal(bd->max, bd->min);
  if(ds) bd->has_single = 1;
  else bd->has_not_single = 1;
  // std::cout <<"-- bd equal: " << ds << std::endl; 
  
  isl_aff_free(bd->max);
  isl_aff_free(bd->min);
  isl_constraint_free(lw);
  isl_constraint_free(up);
  isl_basic_set_free(bset);
  return 0;
}

int find_ineq_cst(__isl_take isl_constraint * c, void * user){

  bd_info * bd = (bd_info *) user;

  int eq;
  if(isl_constraint_involves_dims(c, isl_dim_set, bd->dim, 1)){
    // find constraint is not equality
    eq = isl_constraint_is_equality(c);
    isl_constraint_free(c);  
    if(eq){
      return 0;
    }
    else{
      return -1;
    }
  }

  isl_constraint_free(c);  
  return 0;

}

// Scan bset for single dim
int scan_bset_for_single_dim(__isl_take isl_basic_set *bset, void *user){

  bd_info * bd = (bd_info *) user;

  //isl_basic_set_dump(bset);
  //check each bset
  //int s1 = isl_basic_set_foreach_bound_pair(bset, isl_dim_set, bd->dim, cmp_bound_pair, bd);
  int s1 = isl_basic_set_foreach_constraint(bset, find_ineq_cst, bd);

  isl_basic_set_free(bset);
  return s1;
}

// check whether the specific dimension of the set is single-valued
int check_dim_single(__isl_keep isl_set * dom, int pos){

  // first check by lex points
  // isl_pw_aff * dim_min = isl_set_dim_min(isl_set_copy(dom), pos); 
  // isl_pw_aff * dim_max = isl_set_dim_max(isl_set_copy(dom), pos);
  // int ds = isl_pw_aff_is_equal(dim_min, dim_max);
  // isl_pw_aff_free(dim_min);
  // isl_pw_aff_free(dim_max);
  
  // second check by dim bounds
  //sensitive to any bset not single
  //empty set will get 1 as well !!!
  bd_info bd;
  bd.has_single = 0;
  bd.has_not_single = 0;
  bd.dim = pos;
  int s1 = isl_set_foreach_basic_set(dom, scan_bset_for_single_dim, &bd);

  //if(ds == 1 && bd.has_not_single == 0){
  if(s1 == 0){  
    return 1;
  }
  else{
    return 0;
  }
}

// seperate single basic sets 
int seperate_singles(__isl_take isl_basic_set *bset, void *user){

  dom_sep * sep = (dom_sep *) user;

  isl_set * tmp_set = isl_set_from_basic_set(bset);
  int s = check_dim_single(tmp_set, sep->i_dim);

  if(s){
    sep->dom_s = isl_set_union(sep->dom_s, tmp_set);
    sep->s = 1;
  }
  else{
    sep->dom_n = isl_set_union(sep->dom_n, tmp_set);
  }
  
  return 0;
}



int inc_dim(__isl_take isl_constraint * c, void * user){

  sch_info * sch = (sch_info *) user; 
  
  //isl_constraint_dump(c);
  if(isl_constraint_involves_dims(c, isl_dim_out, (sch->d+1) * 2, 1)){
    isl_val * val = isl_constraint_get_constant_val(c);
    val = isl_val_sub_ui(val, sch->i); //output dim plus 1
    c = isl_constraint_set_constant_val(c, val);
    sch->bmap = isl_basic_map_add_constraint(sch->bmap, isl_constraint_copy(c));
  }  
  
  isl_constraint_free(c);
  return 0;
}


int sch_inc(__isl_take isl_basic_map * bmap, void * user){

  sch_info * sch = (sch_info *) user;

  sch->bmap = isl_basic_map_copy(bmap); 
  sch->bmap = isl_basic_map_drop_constraints_involving_dims(sch->bmap, isl_dim_out, (sch->d+1) * 2, 1);
  
  int s1 = isl_basic_map_foreach_constraint(bmap, inc_dim, sch);

  sch->sch_map = isl_map_from_basic_map(sch->bmap);
  
  isl_basic_map_free(bmap); 
  return 0;
}

// for schedule map splitting
__isl_give isl_map * sch_modify(__isl_keep isl_map * stmt_sch, __isl_keep isl_set * dom, __isl_keep isl_id * stmt_id, int pos, int i){
  // ?? Problem: scheduling map does not make the loop generated as its tree structre
 
  sch_info sch;
  sch.d = pos;
  sch.i = i;

  //int s1 = isl_map_foreach_basic_map(stmt_sch, sch_inc, &sch);
  sch.sch_map = isl_map_copy(stmt_sch); // use same schedule!!!!!!
    
  // sch.sch_map = isl_map_set_tuple_id(sch.sch_map, isl_dim_in, isl_id_copy(stmt_id));  
  // return isl_map_intersect_domain(sch.sch_map, isl_set_copy(dom));

  return isl_map_set_tuple_id(sch.sch_map, isl_dim_in, isl_id_copy(stmt_id));
}


int dim_zero(__isl_take isl_constraint * c, void * user){

  int * pos = (int *) user;

  int z = 0;
  int n = isl_constraint_dim(c, isl_dim_set);
  
  //for(int i= *pos; (i+1)*2 < n; i++){
  if(isl_constraint_involves_dims(c, isl_dim_out, n-1, 1)){
    isl_val * val = isl_constraint_get_constant_val(c);
    if(isl_val_is_zero(val) == 0){
      z = -1;
    }
    isl_val_free(val);
  }    
    //}
  isl_constraint_free(c);
  return z;
}

int check_bmap_sch_dim(__isl_take isl_basic_map * bmap, void * user){

  int s1 = isl_basic_map_foreach_constraint(bmap, dim_zero, user);
  isl_basic_map_free(bmap);
  return s1;  
}

// check current schedule is the first of its inner-most dim
int sch_dim_zero(__isl_keep isl_map * sch, int pos){

  int s1 = isl_map_foreach_basic_map(sch, check_bmap_sch_dim, &pos);

  // -1 for found non-zero
  if(s1 == -1){
    return 0;
  }
  else{
    return 1;
  }
}


int drop_cst(__isl_take isl_constraint * c, void * user){
  par_info * p = (par_info *) (user);
  // drop conflict region related parameter constraints
  // local space must be same
  p->b = isl_basic_set_drop_constraint(p->b, c);
  return 0;
}

int remove_param(__isl_take isl_basic_set * bset, void * user){
  int s1 = isl_basic_set_foreach_constraint(bset, drop_cst, user);
  isl_basic_set_free(bset);
  return 0;
}

int scan_bset(__isl_take isl_basic_set * bset, void * user){

  par_info * p = (par_info *) (user);

  p->b = isl_basic_set_copy(bset);  
  int s1 = isl_set_foreach_basic_set(p->param, remove_param, p);
  //isl_basic_set_dump(p->b);
  p->dom = isl_set_union(p->dom, isl_set_from_basic_set(p->b));
  
  isl_basic_set_free(bset);
  return 0;
}

// remove conflict region related parameter constraints
__isl_give isl_set * remove_param_cft(__isl_take isl_set * dom, __isl_keep isl_set * param_cft){
  
  par_info p;
  p.dom = isl_set_empty(isl_set_get_space(dom));
  isl_set * dom_uni = isl_set_universe(isl_set_get_space(dom));
  p.param = isl_set_intersect_params(dom_uni, isl_set_complement(isl_set_copy(param_cft)));
  int s1 = isl_set_foreach_basic_set(dom, scan_bset, &p);
  //isl_set_dump(p.dom);
  isl_set_free(dom);
  isl_set_free(p.param);
  p.dom = isl_set_remove_redundancies(p.dom); 
  return isl_set_coalesce(p.dom);
}


int change_stmt_id(__isl_keep pet_expr *expr, void *user){

  isl_id * p_id = (isl_id *) user;

  isl_map * acc_map = pet_expr_access_get_access(expr);
  acc_map = isl_map_set_tuple_id(acc_map, isl_dim_in, isl_id_copy(p_id));
  expr = pet_expr_access_set_access(expr, acc_map);
  
  return 0;
}


int blk_cst(__isl_take isl_constraint * c, void * user){
  blk_info * blk = (blk_info *) (user);

  if(isl_constraint_involves_dims(c, isl_dim_set, blk->pos + 1, 1)){
    // copy conflict(innermost) dim bounds to new dim
    isl_constraint * b_cst = isl_constraint_copy(c);
    isl_val * v = isl_constraint_get_coefficient_val(b_cst, isl_dim_set, blk->pos + 1);
    b_cst = isl_constraint_set_coefficient_si(b_cst, isl_dim_set, blk->pos + 1, 0);
    b_cst = isl_constraint_set_coefficient_val(b_cst, isl_dim_set, blk->pos, v);
    blk->bset = isl_basic_set_add_constraint(blk->bset, b_cst);    

    // drop conflict(innermost) dim lower bound
    if( isl_constraint_is_lower_bound(c, isl_dim_set, blk->pos + 1) ){
      blk->bset = isl_basic_set_drop_constraint(blk->bset, isl_constraint_copy(c));      
    }        
  }

  isl_constraint_free(c);
  return 0;
}

int blk_bounds(__isl_take isl_basic_set * bset, void * user){
  blk_info * blk = (blk_info *) (user);

  blk->bset = isl_basic_set_copy(bset);
  
  int s1 = isl_basic_set_foreach_constraint(bset, blk_cst, user);

  blk->dom = isl_set_union(blk->dom, isl_set_from_basic_set(blk->bset));
  
  isl_basic_set_free(bset);  
  return 0;
}

int dim_blk(__isl_take isl_set * set, __isl_take isl_aff * aff, void * user){

  blk_info * blk = (blk_info *) user;

  std::cout << "*** current param piece: " << std::endl;
  isl_set_dump(set);
  std::cout << "*** current dist affine: " << std::endl;
  isl_aff_dump(aff);  
    
  // set up space
  isl_space * sp = isl_set_get_space(set);
  isl_local_space * lsp = isl_local_space_from_space(sp);
  
  // check distance = 1
  isl_ctx * ctx = isl_local_space_get_ctx(lsp);
  isl_val * one = isl_val_one(ctx);
  isl_aff * aff_one = isl_aff_val_on_domain(lsp, one);
  
  // find the piece when distance = 1
  if(isl_aff_plain_is_equal(aff, aff_one) == 1){
    std::cout << "*** find dist == 1" << std::endl;
    blk->slw_dom = isl_set_union(blk->slw_dom, set);    
    isl_aff_free(aff);
    isl_aff_free(aff_one);
    std::cout << "*** finish current piece ***" << std::endl;
    return 0;    
  }  
  isl_aff_free(aff_one);

  // insert block dim in dist
  set = isl_set_insert_dims(set, isl_dim_set, blk->pos, 1);
  aff = isl_aff_insert_dims(aff, isl_dim_in, blk->pos, 1);

  // copy aff coefficient of splitted dim to new blk dim
  isl_val * v = isl_aff_get_coefficient_val(aff, isl_dim_in, blk->pos+1);
  aff = isl_aff_set_coefficient_val(aff, isl_dim_in, blk->pos, v);
  aff = isl_aff_set_coefficient_si(aff, isl_dim_in, blk->pos+1, 0);

  // copy div
  //isl_aff * div = isl_aff_get_div(aff, 0);
  int num_div = isl_aff_dim(aff, isl_dim_div);
  std::cout << "*** num div: " << num_div << std::endl;
  for(int i=0; i<num_div; i++){
    isl_aff * div = isl_aff_get_div(aff, 0);
    v = isl_aff_get_coefficient_val(div, isl_dim_in, blk->pos+1);    
    if(isl_val_is_zero(v) == 0){
      std::cout << "*** find div at conflict dim" << std::endl;
      isl_aff_dump(div);
      div = isl_aff_set_coefficient_val(div, isl_dim_in, blk->pos, v);
      div = isl_aff_set_coefficient_si(div, isl_dim_in, blk->pos+1, 0);
      isl_aff_dump(div);
      aff = isl_aff_drop_dims(aff, isl_dim_div, i, 1);
      isl_aff_dump(aff);
      div = isl_aff_floor(div);
      aff = isl_aff_add(aff, div);
      isl_aff_dump(aff);
    }
    else{
      isl_val_free(v);
      isl_aff_dump(div);
    }
  }

  //assert(false);
  
  // add to new dist
  isl_pw_aff * p_aff = isl_pw_aff_from_aff(isl_aff_copy(aff));
  p_aff = isl_pw_aff_intersect_params(p_aff, isl_set_copy(set));
  blk->dist = isl_pw_aff_union_min(blk->dist, p_aff);
  
  // create new upper bound
  sp = isl_set_get_space(set);
  lsp = isl_local_space_from_space(sp);
  isl_aff * itr = isl_aff_var_on_domain(isl_local_space_copy(lsp), isl_dim_set, blk->pos+1);
  isl_aff * new_itr = isl_aff_var_on_domain(lsp, isl_dim_set, blk->pos);
  
  // itr <= new_itr + dist - 1
  // new_itr - itr + dist - 1 >= 0
  itr = isl_aff_sub(new_itr, itr);
  itr = isl_aff_add(itr, aff);
  isl_constraint * cst = isl_inequality_from_aff(itr);  
  isl_val * c_val = isl_constraint_get_constant_val(cst);
  int c_num = isl_val_get_num_si(c_val);
  isl_val_free(c_val);
  cst = isl_constraint_set_constant_si(cst, c_num - 1);  
  isl_set * dom = isl_set_add_constraint(isl_set_copy(blk->dom), cst);
  
  // add into new domain
  dom = isl_set_intersect_params(dom, set);
  blk->sp_dom = isl_set_union(blk->sp_dom, dom);
  
  //isl_set_dump(blk->sp_dom);
  std::cout << "*** finish current piece *** " << std::endl;
  return 0;
}


/*
 * User defined Scop Modification
 */
int splitLoop(pet_scop * scop, recur_info * rlt){
   
  // Show Conflict Region 
  std::cout << "==== Conflict Region: " << std::endl; 
  isl_set_dump(rlt->cft);

  //remove existentially quantified variables
  isl_set * cft_no_divs = isl_set_remove_divs(isl_set_copy(rlt->cft));
  // isl_set_dump(rlt->cft);
  // isl_set_dump(cft_no_divs);
  // assert(false);
  
  // dimension number of conflict set
  int n_cd = isl_set_dim(rlt->cft, isl_dim_set);
  int n_cp = isl_set_dim(rlt->cft, isl_dim_param);
  
  // Take lex points
  isl_set * cft_lexmin = isl_set_lexmin(isl_set_copy(rlt->cft));
  isl_set * cft_lexmax = isl_set_lexmax(isl_set_copy(rlt->cft));
  std::cout << "==== lexmin point: " << std::endl;   
  isl_set_dump(cft_lexmin); 
  std::cout << "==== lexmax point: " << std::endl;     
  isl_set_dump(cft_lexmax);

  // show scalar dependence distance
  std::cout << "==== dependence distance at conflict dim: " << std::endl;    
  isl_pw_aff_dump(rlt->dist);
  int iter_in_dist = isl_pw_aff_involves_dims(rlt->dist, isl_dim_in, 0, isl_pw_aff_dim(rlt->dist, isl_dim_in));
  std::cout << "** contain iterators : " << iter_in_dist << std::endl;

  // early check dist == 1
  int dist_is_one = 0;
  isl_local_space * dist_lsp = isl_local_space_from_space(isl_pw_aff_get_domain_space(rlt->dist));
  isl_val * val_one = isl_val_one(isl_local_space_get_ctx(dist_lsp));      
  isl_pw_aff * one = isl_pw_aff_from_aff(isl_aff_val_on_domain(dist_lsp, val_one));
  one = isl_pw_aff_intersect_params(one, isl_pw_aff_params(isl_pw_aff_copy(rlt->dist)));        
  if(isl_pw_aff_plain_is_equal(one, rlt->dist) == 1){
    dist_is_one = 1;
  }
  isl_pw_aff_free(one);
  std::cout << "** dist is equal to one: " << dist_is_one << std::endl;
  
  // control the insert of block step statement
  int step_status = 0; 

  std::cout << "==== Outer dimensions have dependence: " << rlt->outer_dep << std::endl; 

  //assert(false);
  
  // statement information
  std::cout << "==== Number of statements in SCoP: "<< scop->n_stmt << std::endl;
  int n_stmt = scop->n_stmt;
  isl_set * stmt_dom_rcd[n_stmt]; //statement domain record
  int i_dim;

  for(int i_st=0; i_st < n_stmt; i_st++){
    //int i_st = 0;

    std::cout << "\n==================== Start statement in SCoP: "<< i_st << " ===================" << std::endl;

    // Copy statement domain
    isl_set * stmt_dom = isl_set_copy(scop->stmts[i_st]->domain);
    isl_set_dump(stmt_dom);
    if(isl_set_is_wrapping(stmt_dom)){
      stmt_dom = isl_map_domain(isl_set_unwrap(stmt_dom));      
    }
    
    stmt_dom_rcd[i_st] = isl_set_copy(stmt_dom);
    stmt_dom = isl_set_reset_tuple_id(stmt_dom);
    std::cout << "==== Statement domain: " << std::endl;
    isl_set_dump(stmt_dom);

    // Copy statement schedule
    isl_map * stmt_sch = isl_map_copy(scop->stmts[i_st]->schedule);
    std::cout << "==== Statement schedule: " << std::endl;
    isl_map_dump(stmt_sch);
    
    // Detect which dimension to be splitted, by lex point comparison
    // more complex cases need for this part!
    std::cout << "==== Search dimension to be splitted " << std::endl;
    int n_dp = isl_set_dim(stmt_dom, isl_dim_param);
    int n_dd = isl_set_dim(stmt_dom, isl_dim_set);
    // int n_d = (n_cd < n_dd) ? n_cd : n_dd;
    
    /*
    isl_set * cd_min;
    isl_set * cd_max;
    isl_set * dd_min;
    isl_set * dd_max;
    int eq_min, eq_max;
    int i_dim = -1;        
    for(int i = n_d-1; i >= 0; i--){
      //for(int i = 0; i < n_d; i++){
      cd_min = isl_set_from_pw_aff(isl_set_dim_min(isl_set_copy(cft_lexmin), i)); 
      dd_min = isl_set_from_pw_aff(isl_set_dim_min(isl_set_copy(stmt_dom), i));
      cd_max = isl_set_from_pw_aff(isl_set_dim_max(isl_set_copy(cft_lexmax), i)); 
      dd_max = isl_set_from_pw_aff(isl_set_dim_max(isl_set_copy(stmt_dom), i));
      
      cd_min = isl_set_eliminate(cd_min, isl_dim_param, 0, n_cp);
      cd_max = isl_set_eliminate(cd_max, isl_dim_param, 0, n_cp);
      dd_min = isl_set_eliminate(dd_min, isl_dim_param, 0, n_dp);
      dd_max = isl_set_eliminate(dd_max, isl_dim_param, 0, n_dp);

      isl_set_dump(cd_min);
      isl_set_dump(cd_max);
      isl_set_dump(dd_min);
      isl_set_dump(dd_max);
      
      eq_min = isl_set_is_equal(cd_min, dd_min); 
      eq_max = isl_set_is_equal(cd_max, dd_max);            

      isl_set_free(cd_min);
      isl_set_free(cd_max);
      isl_set_free(dd_min);
      isl_set_free(dd_max);
      if(eq_min == 0 || eq_max == 0){
    	i_dim = i;
    	break;
      }
    }
    */

    // detect bound aff
    int n_d = (n_cd < n_dd) ? n_cd : n_dd;
    i_dim = -1;
    // isl_aff * s_dsize;
    // isl_aff * c_dsize;
    int eq_d;
    isl_set * sdom_no_divs = isl_set_remove_divs(isl_set_copy(stmt_dom));
    for(int i = n_d-1; i >= 0; i--){
      std::cout << "*** Dim : " << i << " ***"<< std::endl;
      // std::cout << "** stmt : "  << std::endl;
      // s_dsize = get_dim_size(sdom_no_divs, i);
      // std::cout << "** cft : " << std::endl;
      // c_dsize = get_dim_size(cft_no_divs, i);
      // eq_d = isl_aff_plain_is_equal(s_dsize, c_dsize);
      // isl_aff_free(s_dsize);
      // isl_aff_free(c_dsize);
      eq_d = compare_dim_size(sdom_no_divs, cft_no_divs, i);
      if(eq_d == 0){
    	i_dim = i;
    	break;
      }
    }
    isl_set_free(sdom_no_divs);
    
    std::cout << "==== Dimension to be splitted: " << i_dim << std::endl;

    // no need to cut current dom, skip to next stmt
    if(i_dim == -1){
      isl_set_free(stmt_dom);
      isl_map_free(stmt_sch);
      continue;
    }
    
    // dependency locates in the inner-most dimension and across the outer dimension
    if(i_dim == n_cd-1 && rlt->outer_dep == 1){
    //if(rlt->outer_dep == 1){
      std::cout << "\n======= Cut innermost dimension by unflatten loop " << std::endl;

      std::cout << "\n================= Modify SCoP =================" << std::endl;
      //int ui_st = scop->n_stmt;
      //scop->n_stmt = scop->n_stmt + 1;

      // alloc new space
      isl_ctx * ctx = pet_tree_get_ctx(scop->stmts[i_st]->body);
      //scop->stmts = isl_realloc(ctx, scop->stmts, struct pet_stmt *, sizeof(struct pet_stmt *) * scop->n_stmt);
      
      // whether the first stmt at its inner-most dim of stmt schedule map
      int sch_dim_first = sch_dim_zero(stmt_sch, i_dim);
      std::cout << "===== Current stmt is the first of its inner-most schedule dim: " << sch_dim_first << std::endl;
      isl_map_dump(stmt_sch);

      /**************
       **  Part 1: unflatten
       **************/
      std::cout << "\n======= Part 1 " << std::endl;
      std::cout << "*** Domain: " << std::endl;
      isl_id * stmt_id = isl_set_get_tuple_id(stmt_dom_rcd[i_st]);

      // apply id label for apply pragma
      isl_id * p_id;
      if(sch_dim_first == 1){
	std::string p1_str;
	// for unflatten loop 
	p1_str.assign("unflt_");
	p1_str.append(isl_id_get_name(stmt_id));		   
	p_id = isl_id_alloc(ctx, p1_str.c_str(), NULL);
      }
      else{
	// no need to add "flw_" as done for P2 & P3
	p_id = isl_id_copy(stmt_id);
      }

      // add p1 id
      isl_set * dom_1 = isl_set_intersect_params(isl_set_copy(stmt_dom), isl_set_complement(isl_set_copy(rlt->param)));
      dom_1 = isl_set_set_tuple_id(dom_1, isl_id_copy(p_id));
      isl_set_free(scop->stmts[i_st]->domain);
      scop->stmts[i_st]->domain = isl_set_copy(dom_1);
      isl_set_dump(scop->stmts[i_st]->domain);
      //isl_set_free(dom_2);
  
      std::cout << "*** Schedule: " << std::endl;
      scop->stmts[i_st]->schedule = sch_modify(stmt_sch, dom_1, p_id, i_dim, 0);
      isl_map_dump(scop->stmts[i_st]->schedule);
      isl_id_free(p_id);
      isl_set_free(dom_1);
     
      isl_id_free(stmt_id);
      isl_set_free(stmt_dom);
      isl_map_free(stmt_sch);
      continue;
    }
    
    //assert(false);

    /*
    // cut conflict dimension (innermost) by blocks
    //if(iter_in_dist != 1 && i_dim == n_dd-1){
    if(iter_in_dist != 1 && dist_is_one == 0){
      std::cout << "\n======= Cut conflict (innermost) dimension by blocks: " << std::endl;
      rlt->blk_pos = i_dim;
      isl_set * slw_dom = isl_set_copy(stmt_dom);
      isl_map * slw_sch = isl_map_copy(stmt_sch);
      
      std::cout << "==== insert block dim in stmt_dom: " << std::endl;
      stmt_dom = isl_set_insert_dims(stmt_dom, isl_dim_set, i_dim, 1);
      isl_set_dump(stmt_dom);

      // modify domain bounds
      blk_info blk;
      blk.dom = isl_set_empty(isl_set_get_space(stmt_dom));
      blk.pos = i_dim;
      int s_blk  = isl_set_foreach_basic_set(stmt_dom, blk_bounds, &blk);
      isl_set_free(stmt_dom);
      stmt_dom = isl_set_copy(blk.dom);
      isl_set_free(blk.dom);
      isl_set_dump(stmt_dom);

      // set lower bound of conflict(innermost) dim to new dim iterator
      std::cout << "==== split conflict dimension with new lower bound: " << std::endl;
      isl_space * sp = isl_set_get_space(stmt_dom);
      isl_local_space * lsp = isl_local_space_from_space(sp);        
      isl_aff * itr = isl_aff_var_on_domain(isl_local_space_copy(lsp), isl_dim_set, i_dim+1);
      isl_aff * new_itr = isl_aff_var_on_domain(lsp, isl_dim_set, i_dim);
      // itr-new_iter >= 0
      itr = isl_aff_sub(itr, isl_aff_copy(new_itr));
      isl_constraint * cst = isl_inequality_from_aff(itr);
      stmt_dom = isl_set_add_constraint(stmt_dom, cst);
      isl_set_dump(stmt_dom);
      //assert(false);

      // add new upper bound with dep distance
      std::cout << "==== split conflict dimension with additional upper bound: " << std::endl;
      blk.dom = isl_set_copy(stmt_dom);
      blk.sp_dom = isl_set_empty(isl_set_get_space(stmt_dom));
      blk.slw_dom = isl_set_empty(isl_set_get_space(slw_dom));

      // match dim, only drop additional dims in distance
      // Not consider: dims in dist < dom !!!!!!!
      std::cout << "== match dims of dist: " << std::endl;
      isl_pw_aff * dist = isl_pw_aff_copy(rlt->dist);
      int e = isl_set_dim(blk.dom, isl_dim_set) -1; // minus one blk dim 
      int d = isl_pw_aff_dim(dist, isl_dim_in) - e;
      if(d>0){
	dist = isl_pw_aff_drop_dims(dist, isl_dim_in, e, d);
      }
      isl_pw_aff_dump(dist);
      
      // add blk bound
      s_blk = isl_pw_aff_foreach_piece(dist, dim_blk, &blk);

      // add new doms
      std::cout << "== new dom: " << std::endl;
      isl_set_free(stmt_dom);
      stmt_dom = isl_set_copy(blk.sp_dom);
      isl_set_free(blk.dom);
      isl_set_free(blk.sp_dom);      
      stmt_dom = isl_set_remove_redundancies(stmt_dom);
      stmt_dom = isl_set_coalesce(stmt_dom);
      isl_set_dump(stmt_dom);

      std::cout << "== slow dom: " << std::endl;
      isl_set_dump(slw_dom);
      isl_set_dump(blk.slw_dom);
      slw_dom = isl_set_intersect_params(slw_dom, blk.slw_dom);
      slw_dom = isl_set_remove_redundancies(slw_dom);
      slw_dom = isl_set_coalesce(slw_dom);
      isl_set_dump(slw_dom);
      
      std::cout << "==== insert block dim in stmt_sch: " << std::endl;
      stmt_sch = isl_map_reset_tuple_id(stmt_sch, isl_dim_in);
      stmt_sch = isl_map_insert_dims(stmt_sch, isl_dim_in, i_dim, 1);
      isl_map * step_sch = isl_map_insert_dims(isl_map_copy(stmt_sch), isl_dim_out, 2*i_dim+1, 2);
      stmt_sch = isl_map_insert_dims(stmt_sch, isl_dim_out, 2*i_dim+1, 2);
      lsp = isl_local_space_from_space(isl_map_get_space(stmt_sch));
      // new dim
      cst = isl_equality_alloc(isl_local_space_copy(lsp));
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_in, i_dim, 1);
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_out, 2*i_dim+1, -1);
      isl_constraint_dump(cst);
      stmt_sch = isl_map_add_constraint(stmt_sch, cst);
      // new dim sch for body
      cst = isl_equality_alloc(lsp);
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_out, 2*i_dim+2, 1);
      cst = isl_constraint_set_constant_si(cst, 0);
      isl_constraint_dump(cst);
      stmt_sch = isl_map_add_constraint(stmt_sch, cst);
      std::cout << "== new sch: " << std::endl;
      isl_map_dump(stmt_sch);
      
      // new dim sch for step
      std::cout << "== step sch: " << std::endl;      
      lsp = isl_local_space_from_space(isl_map_get_space(step_sch));
      cst = isl_equality_alloc(isl_local_space_copy(lsp));
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_in, i_dim, 1);
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_out, 2*i_dim+1, -1);
      isl_constraint_dump(cst);
      step_sch = isl_map_add_constraint(step_sch, cst);
      isl_map_dump(step_sch);
      cst = isl_equality_alloc(lsp); 
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_out, 2*i_dim+2, 1);
      cst = isl_constraint_set_constant_si(cst, -1);
      isl_constraint_dump(cst);
      step_sch = isl_map_add_constraint(step_sch, cst);
      isl_map_remove_dims(step_sch, isl_dim_out, 2*i_dim+3, isl_map_dim(step_sch, isl_dim_out) - 2*i_dim-3);
      isl_map_dump(step_sch);
      
      //assert(false);

      std::cout << "\n================= Modify SCoP =================" << std::endl;

      // alloc new space
      isl_ctx * ctx = pet_tree_get_ctx(scop->stmts[i_st]->body);
      //scop->stmts = isl_realloc(ctx, scop->stmts, struct pet_stmt *, sizeof(struct pet_stmt *) * scop->n_stmt);
      
      // whether the first stmt at its inner-most dim of stmt schedule map
      int sch_dim_first = sch_dim_zero(stmt_sch, i_dim+1);
      std::cout << "===== Current stmt is the first of its inner-most schedule dim: " << sch_dim_first << std::endl;
      isl_map_dump(stmt_sch);
      
      // ******************************************
      // **  Part 1: Split by blocks
      // *****************************************
      std::cout << "\n======= Part 1 " << std::endl;
      std::cout << "*** Domain: " << std::endl;
      isl_id * stmt_id = isl_set_get_tuple_id(stmt_dom_rcd[i_st]);

      // apply id label for apply pragma
      isl_id * p_id;
      if(sch_dim_first == 1){
	std::string p1_str;
	// for unflatten loop 
	p1_str.assign("p1_");
	p1_str.append(isl_id_get_name(stmt_id));		   
	p_id = isl_id_alloc(ctx, p1_str.c_str(), NULL);
      }
      else{
	// no need to add "flw_" as done for P2 & P3
	p_id = isl_id_copy(stmt_id);
      }

      // add p1 id
      isl_set * dom_1 = isl_set_copy(stmt_dom);
      dom_1 = isl_set_set_tuple_id(dom_1, isl_id_copy(p_id));
      isl_set_free(scop->stmts[i_st]->domain);
      scop->stmts[i_st]->domain = isl_set_copy(dom_1);
      isl_set_dump(scop->stmts[i_st]->domain);
      isl_set_free(dom_1);
  
      std::cout << "*** Schedule: " << std::endl;
      isl_map_free(scop->stmts[i_st]->schedule);
      scop->stmts[i_st]->schedule = isl_map_set_tuple_id(isl_map_copy(stmt_sch), isl_dim_in, isl_id_copy(p_id));
      isl_map_dump(scop->stmts[i_st]->schedule);
      isl_id_free(p_id);


      // ******************************************
      // **  Part 1.1: Step Increment Expression
      // ******************************************
      if(sch_dim_first == 1 && step_status == 0){
	step_status = 1;
	
	std::cout << "\n======= Part 1.1 " << std::endl;
	int ui_st = scop->n_stmt;
	scop->n_stmt = scop->n_stmt + 1;
	scop->stmts[ui_st] = isl_alloc_type(ctx, struct pet_stmt);
	scop->stmts[ui_st]->loc = scop->stmts[i_st]->loc;
	
	std::cout << "*** Copy args: " << std::endl;
	scop->stmts[ui_st]->n_arg = 0;
	std::cout << "number of args: " << scop->stmts[i_st]->n_arg << std::endl;

	std::cout << "*** Domain: " << std::endl;
	// set specific id name for the first splitted stmt
	std::string p2_str;
	p2_str.assign("flw_blk");
	p_id = isl_id_alloc(ctx, p2_str.c_str(), NULL);
	isl_set * dom_step = isl_set_copy(stmt_dom);
	dom_step = isl_set_eliminate(dom_step, isl_dim_set, i_dim+1, isl_set_dim(dom_step, isl_dim_set)-1 - i_dim);
	dom_step = isl_set_set_tuple_id(dom_step, isl_id_copy(p_id));
	scop->stmts[ui_st]->domain = isl_set_copy(dom_step);  
	isl_set_dump(scop->stmts[ui_st]->domain);
	isl_set_free(dom_step);
      
	std::cout << "*** Schedule: " << std::endl;
	scop->stmts[ui_st]->schedule = isl_map_set_tuple_id(isl_map_copy(step_sch), isl_dim_in, isl_id_copy(p_id));
	isl_map_dump(scop->stmts[ui_st]->schedule);
	
	std::cout << "*** Stmt body: " << std::endl;	
	pet_expr * one = pet_expr_new_int(isl_val_one(ctx));
        dist = isl_pw_aff_insert_dims(dist, isl_dim_in, i_dim, 1);
	dist = isl_pw_aff_set_tuple_id(dist, isl_dim_in, isl_id_copy(p_id));
	isl_multi_pw_aff * index = isl_multi_pw_aff_from_pw_aff(isl_pw_aff_copy(dist));
	isl_multi_pw_aff_dump(index);
	isl_map * access = isl_map_from_pw_aff(isl_pw_aff_copy(dist));
	isl_map_dump(access);      
	pet_expr * step = pet_expr_from_access_and_index(access, index);
	step = pet_expr_new_binary(-32, pet_op_sub, step, one);

	new_itr = isl_aff_set_tuple_id(new_itr, isl_dim_set, isl_id_copy(p_id));
	access = isl_map_from_aff(isl_aff_copy(new_itr));
	index = isl_multi_pw_aff_from_pw_aff(isl_pw_aff_from_aff(isl_aff_copy(new_itr)));
	pet_expr * blk_itr = pet_expr_from_access_and_index(access, index);

	blk_itr = pet_expr_new_binary(-32, pet_op_add_assign, blk_itr, step);
	pet_expr_dump_with_indent(blk_itr, 0);
      
	scop->stmts[ui_st]->body = pet_tree_new_expr(blk_itr);
	scop->stmts[ui_st]->body->loc = scop->stmts[i_st]->loc;

	isl_id_free(p_id);
      }
      isl_aff_free(new_itr);
      isl_map_free(step_sch);
      isl_pw_aff_free(dist);
      //assert(false);

      
      // ******************************************
      // **  Part 2 : slow when dist == 1
      // ******************************************
      if(isl_set_is_empty(slw_dom) == 0){
	
	std::cout << "\n======= Part 2 " << std::endl;
	int ui_st = scop->n_stmt;
	scop->n_stmt = scop->n_stmt + 1;
	scop->stmts[ui_st] = isl_alloc_type(ctx, struct pet_stmt);
	scop->stmts[ui_st]->loc = scop->stmts[i_st]->loc;

	std::cout << "*** Copy args: " << std::endl;
	scop->stmts[ui_st]->n_arg = scop->stmts[i_st]->n_arg;
	std::cout << "number of args: " << scop->stmts[i_st]->n_arg << std::endl;
    
	scop->stmts[ui_st]->args = isl_alloc(ctx, pet_expr *, sizeof(pet_expr *) * scop->stmts[ui_st]->n_arg);
	if((scop->stmts[i_st]->n_arg) > 0){
	  for(int i=0; i< (scop->stmts[i_st]->n_arg) -1; i++){
	    std::cout << "Args:  " << i << std::endl;
	    scop->stmts[ui_st]->args[i] = pet_expr_copy(scop->stmts[i_st]->args[i]);
	  }    
	}  

	std::cout << "*** Domain: " << std::endl;
	// set specific id name for the first splitted stmt
	std::string p2_str;
	if(sch_dim_first == 1){
	  //if(i_dim != n_cd-1)
	  p2_str.assign("p2_");
	}
	else{
	  p2_str.assign("flw_p2_");
	}
	p2_str.append(isl_id_get_name(stmt_id));
	p_id = isl_id_alloc(ctx, p2_str.c_str(), NULL);
	isl_set * dom_2 = isl_set_copy(slw_dom);
	dom_2 = isl_set_set_tuple_id(dom_2, isl_id_copy(p_id));
	scop->stmts[ui_st]->domain = isl_set_copy(dom_2);
	isl_set_dump(scop->stmts[ui_st]->domain);
	isl_set_free(dom_2);

	std::cout << "*** Schedule: " << std::endl;
	scop->stmts[ui_st]->schedule = isl_map_set_tuple_id(isl_map_copy(slw_sch), isl_dim_in, isl_id_copy(p_id));
	isl_map_dump(scop->stmts[ui_st]->schedule);

	std::cout << "*** Stmt body: " << std::endl;
	scop->stmts[ui_st]->body = pet_tree_copy(scop->stmts[i_st]->body);
	//s1 = pet_tree_foreach_access_expr(scop->stmts[ui_st]->body, change_stmt_id, p_id);
	isl_id_free(p_id);
      }

      //assert(false);
      
      isl_id_free(stmt_id);
      isl_set_free(stmt_dom);
      isl_set_free(slw_dom);
      isl_map_free(stmt_sch);
      isl_map_free(slw_sch);
      continue;
      
    }
    */

    // Match iterators
    unsigned len = (n_cd < n_dd) ? (n_dd - n_cd) : (n_cd - n_dd);
    isl_set * cft;
    isl_set * pnt_lexmin;
    isl_set * pnt_lexmax;  
    if(n_cd != n_dd){
      cft = isl_set_remove_dims(isl_set_copy(rlt->cft), isl_dim_set, n_d, len);
      pnt_lexmin = isl_set_remove_dims(isl_set_copy(cft_lexmin), isl_dim_set, n_d, len);
      pnt_lexmax = isl_set_remove_dims(isl_set_copy(cft_lexmax), isl_dim_set, n_d, len);
    }
    else{
      cft = isl_set_copy(rlt->cft);
      pnt_lexmin = isl_set_copy(cft_lexmin);
      pnt_lexmax = isl_set_copy(cft_lexmax);	
    }

    // detect single dim in conflict region
    int ds_cft = check_dim_single(cft, i_dim); //found any single dim
    std::cout << "==== The dim will be splitted by one point : " << ds_cft << std::endl;
   
    //assert(false);
    
    // Cut loop dimension i_dim by the LEXMAX point
    std::cout << "\n======= Start domain cut by lexmax of conflict region =======" << std::endl;
    cst_info info;
    info.i_dim = i_dim;
    info.stmt_dom = isl_set_copy(stmt_dom);
    //info.new_dom = isl_set_copy(stmt_dom);
    info.n_bst = 0;
    int s1;
    if(ds_cft){
      s1 = isl_set_foreach_basic_set(cft, constraint_scan, &info);
    }
    else{
      s1 = isl_set_foreach_basic_set(pnt_lexmax, constraint_scan, &info);
    }
    isl_set * dom_lexmax = isl_set_copy(info.new_dom);
    std::cout << "======= End domain cut by lexmax of conflict region =======" << std::endl;
    isl_set_dump(dom_lexmax);
    isl_set_free(info.new_dom);

    // Cut loop dimension i_dim by the LEXMIN point
    std::cout << "\n======= Start domain cut by lexmin of conflict region ======" << std::endl;
    //info.new_dom = isl_set_copy(stmt_dom);
    info.n_bst = 0;
    if(ds_cft){
      s1 = isl_set_foreach_basic_set(cft, constraint_scan, &info);
    }
    else{
      s1 = isl_set_foreach_basic_set(pnt_lexmin, constraint_scan, &info);
    }
    isl_set * dom_lexmin = isl_set_copy(info.new_dom);
    std::cout << "======= End domain cut by lexmin of conflict region ======" << std::endl;
    isl_set_dump(dom_lexmin);
    isl_set_free(info.new_dom);
    isl_set_free(info.stmt_dom);

    // check whether splitted dim is single valued
    int ds_lexmin = check_dim_single(dom_lexmin, i_dim);
    std::cout << "==== dom_lexmin dim is single: " << ds_lexmin << std::endl;
    

    // Set Subtraction
    std::cout << "\n======= Domain Subtraction  ======" << std::endl;
    // Part 3
    std::cout << "*** Part 3: " << std::endl;
    // isl_set * dom_3 = isl_set_intersect_params(isl_set_copy(stmt_dom), isl_set_complement(isl_set_copy(rlt->param)));
    // dom_3 = isl_set_subtract(dom_3, isl_set_copy(dom_lexmax));
    isl_set * dom_3 = isl_set_subtract(isl_set_copy(stmt_dom), isl_set_copy(dom_lexmax));
    dom_3 = isl_set_remove_redundancies(dom_3);
    dom_3 = isl_set_coalesce(dom_3);
    isl_set_dump(dom_3);

    // check whether splitted dim is single valued
    int ds_3 = check_dim_single(dom_3, i_dim);
    std::cout << "==== dom_3 dim is single: " << ds_3 << std::endl;
    if(ds_3 == 1){
      isl_set_free(dom_3);
      dom_3 = isl_set_empty(isl_set_get_space(stmt_dom));
    }    


    isl_set_dump(dom_3);
  
    //assert(false);
  
    // Part 2
    std::cout << "*** Part 2: " << std::endl;
    isl_set * dom_2;
    if(ds_lexmin == 1 && ds_3 == 1){
      // all in slow
      std::cout << "* all in slow " << std::endl;
      dom_2 = isl_set_copy(stmt_dom);
    }
    else if(ds_lexmin == 1){
      // combine part 1 and 2
      std::cout << "* combine part 1 and part 2" << std::endl;
      dom_2 = isl_set_copy(dom_lexmax);
    }
    else if(ds_3 == 1){
      // combine part 2 and 3
      std::cout << "* combine part 2 and part 3 " << std::endl; 
      // dom_2 = isl_set_intersect_params(isl_set_copy(stmt_dom), isl_set_complement(isl_set_copy(rlt->param)));
      // dom_2 = isl_set_subtract(dom_2, isl_set_copy(dom_lexmin));
      dom_2 = isl_set_subtract(isl_set_copy(stmt_dom), isl_set_copy(dom_lexmin));
    }
    else{
      // just part 2
      std::cout << "* just part 2 " << std::endl;
      dom_2 = isl_set_subtract(isl_set_copy(dom_lexmax), isl_set_copy(dom_lexmin));
    }

    // check dom_2 emptiness
    int emp_2 = isl_set_is_empty(dom_2);
    std::cout << "** dom_2 is empty:  " << emp_2 << std::endl; 
    
    dom_2 = isl_set_remove_redundancies(dom_2);
    dom_2 = isl_set_coalesce(dom_2);
    isl_set_dump(dom_2);
  
    // Part 1
    std::cout << "*** Part 1: " << std::endl;
    isl_set * dom_1;
    if(ds_lexmin != 1){
      dom_1 = isl_set_copy(dom_lexmin);
    }
    else{    
      dom_1 = isl_set_empty(isl_set_get_space(dom_2));
    }


    dom_1 = isl_set_remove_redundancies(dom_1);
    dom_1 = isl_set_coalesce(dom_1);
    isl_set_dump(dom_1);
    

    //Special Case: dom_1 or dom_3 are not fully single
    dom_sep sep;
    if(ds_lexmin != 1 && emp_2 != 1){
      std::cout << "*** Seperate single basic sets of dom_1 " << std::endl;
      sep.i_dim = i_dim;
      sep.s = 0;
      sep.dom_n = isl_set_empty(isl_set_get_space(stmt_dom));
      sep.dom_s = isl_set_empty(isl_set_get_space(stmt_dom));
      s1 = isl_set_foreach_basic_set(dom_1, seperate_singles, &sep);
      if(sep.s){
	std::cout << "* Found single bsets" << std::endl;
	isl_set_free(dom_1);
	dom_1 = isl_set_copy(sep.dom_n);
	dom_2 = isl_set_union(dom_2, sep.dom_s);
	isl_set_free(sep.dom_n);
      }
      else{
	isl_set_free(sep.dom_n);
	isl_set_free(sep.dom_s);
      }
    }
    if(ds_3 != 1 && emp_2 != 1){
      std::cout << "*** Seperate single basic sets of dom_3" << std::endl;
      sep.i_dim = i_dim;      
      sep.s = 0;
      sep.dom_n = isl_set_empty(isl_set_get_space(stmt_dom));
      sep.dom_s = isl_set_empty(isl_set_get_space(stmt_dom));
      s1 = isl_set_foreach_basic_set(dom_3, seperate_singles, &sep);
      if(sep.s){
	std::cout << "* Found single bsets" << std::endl;
	isl_set_free(dom_3);
	dom_3 = isl_set_copy(sep.dom_n);
	dom_2 = isl_set_union(dom_2, sep.dom_s);
	isl_set_free(sep.dom_n);
      }
      else{
	isl_set_free(sep.dom_n);
	isl_set_free(sep.dom_s);
      }
    }
    
    
    // apply conflict region
    //if(emp_2 != 1){
    dom_3 = isl_set_intersect_params(dom_3, isl_set_complement(isl_set_copy(rlt->param)));
    dom_2 = isl_set_intersect_params(dom_2, isl_set_complement(isl_set_copy(rlt->param)));
    dom_1 = isl_set_intersect_params(dom_1, isl_set_complement(isl_set_copy(rlt->param)));
      //}

    // remove conflict region related parameter constraints
    // dom_3 = remove_param_cft(dom_3, rlt->param);
    // dom_2 = remove_param_cft(dom_2, rlt->param);
    // dom_1 = remove_param_cft(dom_1, rlt->param);


    // Check bset number
    int n_bs_1 = isl_set_n_basic_set(dom_1);
    int n_bs_2 = isl_set_n_basic_set(dom_2);
    int n_bs_3 = isl_set_n_basic_set(dom_3);
    int n_bs = n_bs_1 + n_bs_2 + n_bs_3;
    std::cout << "*** Sum of bset number : "<< n_bs << std::endl;
    
    int t = 0;
    if(n_bs_1 > 3 || n_bs_2 > 3 || n_bs_3 > 3){
      //if(n_bs_1 > 4){
      std::cout << "==== Too many basic sets for loop splitting" << std::endl;
      t = 0;
    }
    if((isl_set_is_empty(dom_1) == 1 ) && (isl_set_is_empty(dom_3) == 1)){
      // Special Case: dom_1 and dom_3 are all empty
      std::cout << "==== Part 1 and Part 3 are all empty: Apply parametric loop pipelining" << std::endl;
      t = 0;
    }

    // terminate early for applying parametric loop pipelining
    if(t){
      // recover statement counter and domains
      scop->n_stmt = n_stmt;
      for(int j=0; j<i_st; j++){
	isl_set_free(scop->stmts[j]->domain);
	scop->stmts[j]->domain = isl_set_copy(stmt_dom_rcd[j]);
	isl_set_free(stmt_dom_rcd[j]);
      }
      // not fully cleaned !!!!!!!!!!!!
      isl_set_free(stmt_dom_rcd[i_st]);
      isl_set_free(dom_3);
      isl_set_free(dom_2);
      isl_set_free(dom_1);
      isl_set_free(stmt_dom);  
      isl_map_free(stmt_sch);  
      isl_set_free(dom_lexmax);
      isl_set_free(dom_lexmin);
      isl_set_free(pnt_lexmin);
      isl_set_free(pnt_lexmax);
      return 1;
    }

    
    // simplify set representation
    dom_1 = isl_set_remove_redundancies(dom_1);
    dom_1 = isl_set_coalesce(dom_1);
    dom_2 = isl_set_remove_redundancies(dom_2);
    dom_2 = isl_set_coalesce(dom_2);
    dom_3 = isl_set_remove_redundancies(dom_3);
    dom_3 = isl_set_coalesce(dom_3);
    std::cout << "\n*** Dom 1: " << std::endl;
    isl_set_dump(dom_1);
    // isl_val * cnt1 = isl_set_count_val(dom_1);
    // isl_val_dump(cnt1);
    std::cout << "*** Dom 2: " << std::endl;
    isl_set_dump(dom_2);
    // isl_val * cnt2 = isl_set_count_val(dom_2);
    // isl_val_dump(cnt2);
    std::cout << "*** Dom 3: " << std::endl;
    isl_set_dump(dom_3);
    // isl_val * cnt3 = isl_set_count_val(dom_3);
    // isl_val_dump(cnt3);  
        
    //assert(false);
  
    // Modify SCoP
    std::cout << "\n================= Modify SCoP =================" << std::endl;
    int ui_st = scop->n_stmt;
    scop->n_stmt = scop->n_stmt + 2;

    // alloc new space
    isl_ctx * ctx = pet_tree_get_ctx(scop->stmts[i_st]->body);
    scop->stmts = isl_realloc(ctx, scop->stmts, struct pet_stmt *, sizeof(struct pet_stmt *) * scop->n_stmt);

    // whether the first stmt at its inner-most dim of stmt schedule map
    int sch_dim_first = sch_dim_zero(stmt_sch, i_dim);
    std::cout << "===== Current stmt is the first of its inner-most schedule dim: " << sch_dim_first << std::endl;
    isl_map_dump(stmt_sch);

    //assert(false);

    isl_id * stmt_id = isl_set_get_tuple_id(stmt_dom_rcd[i_st]);
    
    /******************************************
     **  Part 1
     ******************************************/
    std::cout << "\n======= Part 1 " << std::endl;
    scop->stmts[ui_st] = isl_alloc_type(ctx, struct pet_stmt);
    scop->stmts[ui_st]->loc = scop->stmts[i_st]->loc;

    std::cout << "*** Copy args: " << std::endl;
    scop->stmts[ui_st]->n_arg = scop->stmts[i_st]->n_arg;
    std::cout << "number of args: " << scop->stmts[i_st]->n_arg << std::endl;
    
    scop->stmts[ui_st]->args = isl_alloc(ctx, pet_expr *, sizeof(pet_expr *) * scop->stmts[ui_st]->n_arg);
    if((scop->stmts[i_st]->n_arg) > 0){
      for(int i=0; i< (scop->stmts[i_st]->n_arg) -1; i++){
	std::cout << "Args:  " << i << std::endl;
	scop->stmts[ui_st]->args[i] = pet_expr_copy(scop->stmts[i_st]->args[i]);
      }    
    }  
    
    std::cout << "*** Domain: " << std::endl;
    // apply id label for apply pragma
    isl_id * p_id;
    std::string p1_str;
    if(sch_dim_first == 1){
      if((ds_cft == 1) && (ds_3 == 1)){
	// for unflatten loop when cut point is at the end of dim
	p1_str.assign("unflt_");
	//assert(false);
      }
      else{
	p1_str.assign("p1_");
      }
    }
    else{
      // no need to add "flw_" as done for P2 & P3
      //p_id = isl_id_copy(stmt_id);
      p1_str.assign("flw_p1_");
    }
    p1_str.append(isl_id_get_name(stmt_id));		   
    p_id = isl_id_alloc(ctx, p1_str.c_str(), NULL);
    
    // add p1 id
    dom_1 = isl_set_set_tuple_id(dom_1, isl_id_copy(p_id));
    //isl_set_free(scop->stmts[ui_st]->domain);
    scop->stmts[ui_st]->domain = isl_set_copy(dom_1);
    isl_set_dump(scop->stmts[ui_st]->domain);
    //isl_set_free(dom_2);
  
    std::cout << "*** Schedule: " << std::endl;
    scop->stmts[ui_st]->schedule = sch_modify(stmt_sch, dom_1, p_id, i_dim, 1);
    isl_map_dump(scop->stmts[ui_st]->schedule);
    isl_id_free(p_id);

    std::cout << "*** Stmt body: " << std::endl;
    scop->stmts[ui_st]->body = pet_tree_copy(scop->stmts[i_st]->body);
    //s1 = pet_tree_foreach_access_expr(scop->stmts[ui_st]->body, change_stmt_id, p_id);
    isl_id_free(p_id);    
    
    /******************************************
     **  Part 2 : Slow Part 
     ******************************************/
    std::cout << "\n======= Part 2 " << std::endl;
    std::cout << "*** Domain: " << std::endl;
    // set specific id name for the first splitted stmt
    std::string p2_str;
    if(sch_dim_first == 1){
      p2_str.assign("p2_");
    }
    else{
      p2_str.assign("flw_p2_");
    }
    p2_str.append(isl_id_get_name(stmt_id));
    p_id = isl_id_alloc(ctx, p2_str.c_str(), NULL);
    dom_2 = isl_set_set_tuple_id(dom_2, isl_id_copy(p_id));
    isl_set_free(scop->stmts[i_st]->domain);
    scop->stmts[i_st]->domain = isl_set_copy(dom_2);  
    isl_set_dump(scop->stmts[i_st]->domain);

    std::cout << "*** Schedule: " << std::endl;
    isl_map_free(scop->stmts[i_st]->schedule);
    scop->stmts[i_st]->schedule = sch_modify(stmt_sch, dom_2, p_id, i_dim, 2);
    isl_map_dump(scop->stmts[i_st]->schedule);
    
    //assert(false);

    /******************************************
     **  Part 3
     ******************************************/
    std::cout << "\n======= Part 3 " << std::endl;
    scop->stmts[ui_st+1] = isl_alloc_type(ctx, struct pet_stmt);
    scop->stmts[ui_st+1]->loc = scop->stmts[i_st]->loc;

    std::cout << "*** Copy args: " << std::endl;
    scop->stmts[ui_st+1]->n_arg = scop->stmts[i_st]->n_arg;
    std::cout << "number of args: " << scop->stmts[i_st]->n_arg << std::endl;
    
    scop->stmts[ui_st+1]->args = isl_alloc(ctx, pet_expr *, sizeof(pet_expr *) * scop->stmts[ui_st+1]->n_arg);
    if((scop->stmts[i_st]->n_arg) > 0){
      for(int i=0; i< (scop->stmts[i_st]->n_arg) -1; i++){
	std::cout << "Args:  " << i << std::endl;
	scop->stmts[ui_st+1]->args[i] = pet_expr_copy(scop->stmts[i_st]->args[i]);
      }    
    }  

    std::cout << "*** Domain: " << std::endl;
    // set specific id name for the first splitted stmt
    std::string p3_str;
    if(sch_dim_first == 1){
      p3_str.assign("p3_");
    }
    else{
      p3_str.assign("flw_p3_");
    }
    p3_str.append(isl_id_get_name(stmt_id));
    p_id = isl_id_alloc(ctx, p3_str.c_str(), NULL);
    dom_3 = isl_set_set_tuple_id(dom_3, isl_id_copy(p_id));
    //dom_3 = isl_set_set_tuple_id(dom_3, isl_id_copy(stmt_id));
    scop->stmts[ui_st+1]->domain = isl_set_copy(dom_3);  
    isl_set_dump(scop->stmts[ui_st+1]->domain);

    std::cout << "*** Schedule: " << std::endl;
    scop->stmts[ui_st+1]->schedule = sch_modify(stmt_sch, dom_3, p_id, i_dim, 3);
    isl_map_dump(scop->stmts[ui_st+1]->schedule);

    std::cout << "*** Stmt body: " << std::endl;
    scop->stmts[ui_st+1]->body = pet_tree_copy(scop->stmts[i_st]->body);
    //s1 = pet_tree_foreach_access_expr(scop->stmts[ui_st+1]->body, change_stmt_id, p_id);
    isl_id_free(p_id);

    isl_set_free(dom_3);
    isl_set_free(dom_2);
    isl_set_free(dom_1);


    // cut conflict dimension (innermost) by blocks
    //if(iter_in_dist != 1 && i_dim == n_dd-1){
    //if(iter_in_dist != 1 && dist_is_one == 0){
    if( dist_is_one == 0){
      std::cout << "\n======= Cut conflict (innermost) dimension by blocks ============" << std::endl;
      rlt->blk_pos = i_dim;
      isl_set_free(stmt_dom);
      stmt_dom =isl_set_reset_tuple_id(isl_set_copy(scop->stmts[i_st]->domain));
      isl_set * slw_dom = isl_set_copy(stmt_dom);
      isl_map * slw_sch = isl_map_copy(stmt_sch);
      
      std::cout << "==== insert block dim in stmt_dom: " << std::endl;
      stmt_dom = isl_set_insert_dims(stmt_dom, isl_dim_set, i_dim, 1);
      isl_set_dump(stmt_dom);

      // modify domain bounds
      blk_info blk;
      blk.dom = isl_set_empty(isl_set_get_space(stmt_dom));
      blk.pos = i_dim;
      int s_blk  = isl_set_foreach_basic_set(stmt_dom, blk_bounds, &blk);
      isl_set_free(stmt_dom);
      stmt_dom = isl_set_copy(blk.dom);
      isl_set_free(blk.dom);
      isl_set_dump(stmt_dom);

      // set lower bound of conflict(innermost) dim to new dim iterator
      std::cout << "==== split conflict dimension with new lower bound: " << std::endl;
      isl_space * sp = isl_set_get_space(stmt_dom);
      isl_local_space * lsp = isl_local_space_from_space(sp);        
      isl_aff * itr = isl_aff_var_on_domain(isl_local_space_copy(lsp), isl_dim_set, i_dim+1);
      isl_aff * new_itr = isl_aff_var_on_domain(lsp, isl_dim_set, i_dim);
      // itr-new_iter >= 0
      itr = isl_aff_sub(itr, isl_aff_copy(new_itr));
      isl_constraint * cst = isl_inequality_from_aff(itr);
      stmt_dom = isl_set_add_constraint(stmt_dom, cst);
      isl_set_dump(stmt_dom);
      //assert(false);

      // add new upper bound with dep distance
      std::cout << "==== split conflict dimension with additional upper bound: " << std::endl;
      blk.dom = isl_set_copy(stmt_dom);
      blk.sp_dom = isl_set_empty(isl_set_get_space(stmt_dom));
      blk.slw_dom = isl_set_empty(isl_set_get_space(slw_dom));
      
      // match dim, only drop additional dims in distance
      // Not consider: dims in dist < dom !!!!!!!
      std::cout << "== match dims of dist: " << std::endl;
      isl_pw_aff * dist = isl_pw_aff_copy(rlt->dist);
      int e = isl_set_dim(blk.dom, isl_dim_set) -1; // minus one blk dim 
      int d = isl_pw_aff_dim(dist, isl_dim_in) - e;
      if(d>0){
	dist = isl_pw_aff_drop_dims(dist, isl_dim_in, e, d);
      }
      isl_pw_aff_dump(dist);
      isl_pw_aff * dist_blk = isl_pw_aff_insert_dims(isl_pw_aff_copy(dist), isl_dim_in, i_dim, 1);
      blk.dist = isl_pw_aff_empty(isl_pw_aff_get_space(dist_blk));
      isl_pw_aff_free(dist_blk);
      
      // add blk bound
      s_blk = isl_pw_aff_foreach_piece(dist, dim_blk, &blk);
      isl_pw_aff_free(dist);
      dist = isl_pw_aff_copy(blk.dist);
      isl_pw_aff_free(blk.dist);
      isl_pw_aff_dump(dist);

      // add new doms
      std::cout << "== new dom: " << std::endl;
      isl_set_free(stmt_dom);
      stmt_dom = isl_set_copy(blk.sp_dom);
      isl_set_free(blk.dom);
      isl_set_free(blk.sp_dom);      
      stmt_dom = isl_set_remove_redundancies(stmt_dom);
      stmt_dom = isl_set_coalesce(stmt_dom);
      isl_set_dump(stmt_dom);

      std::cout << "== slow dom: " << std::endl;
      isl_set_dump(slw_dom);
      isl_set_dump(blk.slw_dom);
      slw_dom = isl_set_intersect_params(slw_dom, blk.slw_dom);
      slw_dom = isl_set_remove_redundancies(slw_dom);
      slw_dom = isl_set_coalesce(slw_dom);
      isl_set_dump(slw_dom);
      
      std::cout << "==== insert block dim in stmt_sch: " << std::endl;
      stmt_sch = isl_map_reset_tuple_id(stmt_sch, isl_dim_in);
      stmt_sch = isl_map_insert_dims(stmt_sch, isl_dim_in, i_dim, 1);
      isl_map * step_sch = isl_map_insert_dims(isl_map_copy(stmt_sch), isl_dim_out, 2*i_dim+1, 2);
      stmt_sch = isl_map_insert_dims(stmt_sch, isl_dim_out, 2*i_dim+1, 2);
      lsp = isl_local_space_from_space(isl_map_get_space(stmt_sch));
      // new dim
      cst = isl_equality_alloc(isl_local_space_copy(lsp));
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_in, i_dim, 1);
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_out, 2*i_dim+1, -1);
      isl_constraint_dump(cst);
      stmt_sch = isl_map_add_constraint(stmt_sch, cst);
      // new dim sch for body
      cst = isl_equality_alloc(lsp);
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_out, 2*i_dim+2, 1);
      cst = isl_constraint_set_constant_si(cst, 0);
      isl_constraint_dump(cst);
      stmt_sch = isl_map_add_constraint(stmt_sch, cst);
      std::cout << "== new sch: " << std::endl;
      isl_map_dump(stmt_sch);
      
      // new dim sch for step
      std::cout << "== step sch: " << std::endl;      
      lsp = isl_local_space_from_space(isl_map_get_space(step_sch));
      cst = isl_equality_alloc(isl_local_space_copy(lsp));
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_in, i_dim, 1);
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_out, 2*i_dim+1, -1);
      isl_constraint_dump(cst);
      step_sch = isl_map_add_constraint(step_sch, cst);
      isl_map_dump(step_sch);
      cst = isl_equality_alloc(lsp); 
      cst = isl_constraint_set_coefficient_si(cst, isl_dim_out, 2*i_dim+2, 1);
      cst = isl_constraint_set_constant_si(cst, -1);
      isl_constraint_dump(cst);
      step_sch = isl_map_add_constraint(step_sch, cst);
      isl_map_remove_dims(step_sch, isl_dim_out, 2*i_dim+3, isl_map_dim(step_sch, isl_dim_out) - 2*i_dim-3);
      isl_map_dump(step_sch);
      
      //assert(false);

      std::cout << "\n================= Split Slow Part by Blocks =================" << std::endl;

      // alloc new space
      isl_ctx * ctx = pet_tree_get_ctx(scop->stmts[i_st]->body);
      //scop->stmts = isl_realloc(ctx, scop->stmts, struct pet_stmt *, sizeof(struct pet_stmt *) * scop->n_stmt);
      
      // whether the first stmt at its inner-most dim of stmt schedule map
      int sch_dim_first = sch_dim_zero(stmt_sch, i_dim+1);
      std::cout << "===== Current stmt is the first of its inner-most schedule dim: " << sch_dim_first << std::endl;
      isl_map_dump(stmt_sch);
      
      /******************************************
       **  Part 2: Split by blocks
       ******************************************/
      std::cout << "\n======= Part 2 " << std::endl;
      std::cout << "*** Domain: " << std::endl;
      //isl_id * stmt_id = isl_set_get_tuple_id(stmt_dom_rcd[i_st]);

      // apply id label for apply pragma
      //isl_id * p_id;
      if(sch_dim_first == 1){
	p2_str.assign("blk_");

      }
      else{
	p2_str.assign("flw_blk_");
	//p_id = isl_id_copy(stmt_id);
      }
      p2_str.append(isl_id_get_name(stmt_id));		   
      p_id = isl_id_alloc(ctx, p2_str.c_str(), NULL);
	
      // add new p2 id
      dom_2 = isl_set_copy(stmt_dom);
      dom_2 = isl_set_set_tuple_id(dom_2, isl_id_copy(p_id));
      isl_set_free(scop->stmts[i_st]->domain);
      scop->stmts[i_st]->domain = isl_set_copy(dom_2);
      isl_set_dump(scop->stmts[i_st]->domain);
      isl_set_free(dom_2);
  
      std::cout << "*** Schedule: " << std::endl;
      isl_map_free(scop->stmts[i_st]->schedule);
      scop->stmts[i_st]->schedule = isl_map_set_tuple_id(isl_map_copy(stmt_sch), isl_dim_in, isl_id_copy(p_id));
      isl_map_dump(scop->stmts[i_st]->schedule);
      isl_id_free(p_id);


      /******************************************
       **  Part 2.1: Step Increment Expression
       ******************************************/
      if(sch_dim_first == 1 && step_status == 0){
	step_status = 1;
	
	std::cout << "\n======= Part 2.1 " << std::endl;
	int ui_st = scop->n_stmt;
	scop->n_stmt = scop->n_stmt + 1;
	scop->stmts[ui_st] = isl_alloc_type(ctx, struct pet_stmt);
	scop->stmts[ui_st]->loc = scop->stmts[i_st]->loc;
	
	std::cout << "*** Copy args: " << std::endl;
	scop->stmts[ui_st]->n_arg = 0;
	std::cout << "number of args: " << scop->stmts[i_st]->n_arg << std::endl;

	std::cout << "*** Domain: " << std::endl;
	// set specific id name for the first splitted stmt
	std::string blk_str;
	blk_str.assign("step_blk");
	p_id = isl_id_alloc(ctx, blk_str.c_str(), NULL);
	isl_set * dom_step = isl_set_copy(stmt_dom);
	dom_step = isl_set_eliminate(dom_step, isl_dim_set, i_dim+1, isl_set_dim(dom_step, isl_dim_set)-1 - i_dim);
	dom_step = isl_set_set_tuple_id(dom_step, isl_id_copy(p_id));
	scop->stmts[ui_st]->domain = isl_set_copy(dom_step);  
	isl_set_dump(scop->stmts[ui_st]->domain);
	isl_set_free(dom_step);
      
	std::cout << "*** Schedule: " << std::endl;
	scop->stmts[ui_st]->schedule = isl_map_set_tuple_id(isl_map_copy(step_sch), isl_dim_in, isl_id_copy(p_id));
	isl_map_dump(scop->stmts[ui_st]->schedule);
	
	std::cout << "*** Stmt body: " << std::endl;
	// step - 1
	pet_expr * one = pet_expr_new_int(isl_val_one(ctx));
        //dist = isl_pw_aff_insert_dims(dist, isl_dim_in, i_dim, 1);
	dist = isl_pw_aff_set_tuple_id(dist, isl_dim_in, isl_id_copy(p_id));
	isl_multi_pw_aff * index = isl_multi_pw_aff_from_pw_aff(isl_pw_aff_copy(dist));
	isl_multi_pw_aff_dump(index);
	isl_map * access = isl_map_from_pw_aff(isl_pw_aff_copy(dist));
	isl_map_dump(access);      
	pet_expr * step = pet_expr_from_access_and_index(access, index);
	step = pet_expr_new_binary(-32, pet_op_sub, step, one);

	// blk iterator
	new_itr = isl_aff_set_tuple_id(new_itr, isl_dim_set, isl_id_copy(p_id));
	access = isl_map_from_aff(isl_aff_copy(new_itr));
	index = isl_multi_pw_aff_from_pw_aff(isl_pw_aff_from_aff(isl_aff_copy(new_itr)));
	pet_expr * blk_itr = pet_expr_from_access_and_index(access, index);

	// blk iterator += step - 1
	blk_itr = pet_expr_new_binary(-32, pet_op_add_assign, blk_itr, step);
	pet_expr_dump_with_indent(blk_itr, 0);
      
	scop->stmts[ui_st]->body = pet_tree_new_expr(blk_itr);
	scop->stmts[ui_st]->body->loc = scop->stmts[i_st]->loc;

	isl_id_free(p_id);
      }
      isl_aff_free(new_itr);
      isl_map_free(step_sch);
      isl_pw_aff_free(dist);
      //assert(false);

      
      /******************************************
       **  Part 2 : slow when dist == 1
       ******************************************/
      if(isl_set_is_empty(slw_dom) == 0){
	
	std::cout << "\n======= Part 2 " << std::endl;
	int ui_st = scop->n_stmt;
	scop->n_stmt = scop->n_stmt + 1;
	scop->stmts[ui_st] = isl_alloc_type(ctx, struct pet_stmt);
	scop->stmts[ui_st]->loc = scop->stmts[i_st]->loc;

	std::cout << "*** Copy args: " << std::endl;
	scop->stmts[ui_st]->n_arg = scop->stmts[i_st]->n_arg;
	std::cout << "number of args: " << scop->stmts[i_st]->n_arg << std::endl;
    
	scop->stmts[ui_st]->args = isl_alloc(ctx, pet_expr *, sizeof(pet_expr *) * scop->stmts[ui_st]->n_arg);
	if((scop->stmts[i_st]->n_arg) > 0){
	  for(int i=0; i< (scop->stmts[i_st]->n_arg) -1; i++){
	    std::cout << "Args:  " << i << std::endl;
	    scop->stmts[ui_st]->args[i] = pet_expr_copy(scop->stmts[i_st]->args[i]);
	  }    
	}  

	std::cout << "*** Domain: " << std::endl;
	// set specific id name for the first splitted stmt
	//std::string p2_str;
	if(sch_dim_first == 1){
	  //if(i_dim != n_cd-1)
	  p2_str.assign("p2_");
	}
	else{
	  p2_str.assign("flw_p2_");
	}
	p2_str.append(isl_id_get_name(stmt_id));
	p_id = isl_id_alloc(ctx, p2_str.c_str(), NULL);
	dom_2 = isl_set_copy(slw_dom);
	dom_2 = isl_set_set_tuple_id(dom_2, isl_id_copy(p_id));
	scop->stmts[ui_st]->domain = isl_set_copy(dom_2);
	isl_set_dump(scop->stmts[ui_st]->domain);
	isl_set_free(dom_2);

	std::cout << "*** Schedule: " << std::endl;
	scop->stmts[ui_st]->schedule = isl_map_set_tuple_id(isl_map_copy(slw_sch), isl_dim_in, isl_id_copy(p_id));
	isl_map_dump(scop->stmts[ui_st]->schedule);

	std::cout << "*** Stmt body: " << std::endl;
	scop->stmts[ui_st]->body = pet_tree_copy(scop->stmts[i_st]->body);
	isl_id_free(p_id);
      }

      //assert(false);
      
      //isl_id_free(stmt_id);
      //isl_set_free(stmt_dom);
      isl_set_free(slw_dom);
      //isl_map_free(stmt_sch);
      isl_map_free(slw_sch);      
    }
    
  
    //assert(false);
    isl_id_free(stmt_id);
    isl_set_free(stmt_dom);  
    isl_map_free(stmt_sch);  
    isl_set_free(dom_lexmax);
    isl_set_free(dom_lexmin);
    isl_set_free(pnt_lexmax);
    isl_set_free(pnt_lexmin);
    isl_set_free(cft);
    
    //isl_ctx_free(ctx);
    std::cout << "==================== End statement in SCoP: "<< i_st << " ===================" << std::endl;
  }

  //assert(false);
  
  for(int i_st=0; i_st<n_stmt; i_st++){
    isl_set_free(stmt_dom_rcd[i_st]);
  }
  isl_set_free(cft_lexmin);
  isl_set_free(cft_lexmax);
  isl_set_free(cft_no_divs);

  // assign return value
  // int rtn_val;
  // if(i_dim == n_cd-1 && rlt->outer_dep == 1){
  //   rtn_val = 0;
  // }
  // else if (iter_in_dist != 1 && dist_is_one == 0){
  //   rtn_val = 3;    
  // }
  // else
  //   rtn_val = 0;
  
  return 0;
}

