#include <potholes/transform.h>
#include <potholes/affine.h>

#include <iostream>

#include </Users/Junyi/research/HLS/pet/expr.h>

#include <isl/ilp.h>
#include <isl/flow.h>
#include <isl/constraint.h>

#include <cassert>

// tansformation constructor
potholes::Transform::Transform(Analysis& analysis) :analysis(analysis) {
              
}


// affine scan
int aff_scan(isl_set *set, isl_aff *aff, void *user){
  
  acc_info *info = (acc_info *) (user);  
  
  // affine
  isl_aff_dump(aff);
  info->aff = isl_aff_copy(aff); 
 
  isl_val * v;

  // parameters
  int n_dim_p = isl_aff_dim(aff, isl_dim_param);
  for(int i=0; i<n_dim_p ;i++){
    v = isl_aff_get_coefficient_val(aff, isl_dim_param, i);
    //isl_val_dump(v);
    info->pt_coeff[i] = isl_val_get_num_si(v);
    isl_val_free(v);
  }
  
  // iterators
  int n_dim_i = isl_aff_dim(aff, isl_dim_in);
  for(int i=0; i<n_dim_i ;i++){
    v = isl_aff_get_coefficient_val(aff, isl_dim_in, i);
    //isl_val_dump(v);
    info->it_coeff[i] = isl_val_get_num_si(v);
    isl_val_free(v);    
  }

  // constant
  v = isl_aff_get_constant_val(aff);
  info->cnt = isl_val_get_num_si(v);
  
  isl_val_free(v);
  isl_aff_free(aff);
  isl_set_free(set);
  return 0;
}


// memory access scan
int acc_expr_scan(pet_expr *expr, void *user){

  stmt_info *info = (stmt_info *) (user);     
  
  // wrapped access checked before
  // skip non-array access
  isl_map * map = pet_expr_access_get_access(expr);  
  if(isl_map_has_tuple_name(map, isl_dim_out) == 0){
    isl_map_free(map);
    std::cout << "###skip non-array access" << std::endl;
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

  //record array name
  acc->name = isl_map_get_tuple_name(map, isl_dim_out);
  //std::cout << "acc_tuple_name: "<< acc->name << std::endl;

  //record array access map
  acc->map = isl_map_copy(map);
  isl_map_dump(acc->map);

  //number of pt and it
  acc->n_pt = isl_map_n_param(map);
  acc->n_it = isl_map_n_in(map);

  // assume just 1 target array access   
  isl_pw_aff * pwaff = isl_multi_pw_aff_get_pw_aff(expr->acc.index, 0);
  
  int success = isl_pw_aff_foreach_piece(pwaff, aff_scan, acc);
  
  // isl_space *p_space = pet_expr_access_get_data_space(pet_expr_copy(expr));
  // isl_space_dump(p_space);
  
  //isl_space_free(access_space);
  isl_map_free(map);
  isl_pw_aff_free(pwaff);
  return 0;
}

// memory access info
int acc_expr_info(pet_expr *expr, void *user){
  
  stmt_info *info = (stmt_info *) (user);
  
  if(expr->n_arg != 0){
    std::cout << "###cannot analyze wrapped access" << std::endl;
    return -1;
  }

  isl_map * map = pet_expr_access_get_access(expr);
  
  if(isl_map_has_tuple_name(map, isl_dim_out) == 0){
    isl_map_free(map);
    std::cout << "###skip non-array access" << std::endl;
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
  return 0;
}

// isl_access_level_before func for dependency analysis
int acc_order(void * first, void * second){

  acc_info * acc_1 = (acc_info *)first;
  
  // set to always on same line
  return 2*(acc_1->n_it)+1;
}

// get the size of the dimention of a given isl_set
isl_val * get_dim_size(__isl_keep isl_set * set, unsigned dim)
{
 
  isl_set * bounded_set = isl_set_project_out(isl_set_copy(set), isl_dim_set, 0, dim);
  isl_set_dump(bounded_set);

  isl_space * bounded_space = isl_set_get_space(bounded_set);
  isl_aff * aff = isl_aff_zero_on_domain(isl_local_space_from_space(bounded_space));

  aff = isl_aff_set_coefficient_si(aff, isl_dim_in, 0, 1);   
  isl_aff_dump(aff);

  isl_val * max = isl_set_max_val(bounded_set, aff);
  isl_val * min = isl_set_min_val(bounded_set, aff);  
  max = isl_val_sub(max,min);

  isl_aff_free(aff);
  return isl_val_add_ui(max, 1); //max-min+1
}

// check multi-affine difference
int check_multi_aff_diff(isl_set * set, isl_multi_aff * maff, void * user){

  stmt_info * stmt = (stmt_info *)user;

  // (src-snk) in multi-afffine
  for(int i=0; i<stmt->n_it; i++){
    isl_aff * snk_aff = isl_multi_aff_get_aff(maff, i);
    isl_aff * src_aff = isl_aff_list_get_aff(stmt->src, i);
    snk_aff = isl_aff_sub(src_aff, snk_aff);
    maff = isl_multi_aff_set_aff(maff, i, snk_aff);
  }
  isl_multi_aff_dump(maff);

  // flatten (src-snk)
  isl_space * sp = isl_set_get_space(isl_set_copy(stmt->domain));
  isl_local_space * lsp = isl_local_space_from_space(sp);
  isl_ctx * ctx = isl_local_space_get_ctx(lsp);
  isl_val * ftr = isl_val_one(ctx);
  isl_aff * diff = isl_aff_zero_on_domain(isl_local_space_copy(lsp));
  for(int i=stmt->n_it-1; i>=0; i--){
    // add dimension item with factor
    isl_aff * dim = isl_multi_aff_get_aff(maff, i);
    dim = isl_aff_scale_val(dim, isl_val_copy(ftr));
    diff = isl_aff_add(diff, dim);
    // scale up factor
    if(i>0){
      ftr = isl_val_mul(ftr, get_dim_size(stmt->domain, i));
      isl_val_dump(ftr);
    }
  }
  isl_aff_dump(diff);
  isl_val_free(ftr);  
  //isl_ctx_free(ctx);
  
  // src-snk + L-1 >=0
  isl_constraint * cst = isl_inequality_from_aff(isl_aff_copy(diff)); 
  // constant += L-1, L is delay cycles, which is >=1 !!!!!!!!!!!!!!!!
  isl_val * c_val = isl_constraint_get_constant_val(cst);
  int c_num = isl_val_get_num_si(c_val);
  isl_val_free(c_val);
  cst = isl_constraint_set_constant_si(cst, c_num + L_delay -1 );
  isl_constraint_dump(cst);
  isl_set * cst_ub = isl_set_from_basic_set(isl_basic_set_from_constraint(cst));

  // snk-src -1 >=0
  // affine: sink-source = distance
  diff = isl_aff_sub(isl_aff_zero_on_domain(lsp), diff); //0 - (src-snk)
  cst = isl_inequality_from_aff(diff);
  // constant += -1
  c_val = isl_constraint_get_constant_val(cst);
  c_num = isl_val_get_num_si(c_val);
  isl_val_free(c_val);
  cst = isl_constraint_set_constant_si(cst, c_num -1 );
  isl_constraint_dump(cst);  
  isl_set * cst_lb = isl_set_from_basic_set(isl_basic_set_from_constraint(cst));    

  // intersect lower and upper bounds
  isl_set * bd = isl_set_intersect(cst_lb, cst_ub);
  isl_set_dump(bd);
  bd = isl_set_intersect(isl_set_copy(stmt->domain), bd);
  isl_set_dump(bd);

  // ** check emptiness for whether further check parameters
  isl_set * empty;
  bd = isl_set_partial_lexmax(bd, isl_set_copy(stmt->context), &empty);
  isl_set_dump(bd);
  isl_set_dump(empty);

  if(stmt->param == NULL){
    stmt->param = isl_set_copy(empty);
  }
  else{
    stmt->param = isl_set_intersect(stmt->param,isl_set_copy(empty));
  }
  //stmt->param = isl_set_params(*empty);

  //assert(false);

  //isl_set_dump(stmt->param); 
  isl_set_free(empty);
  isl_set_free(bd);
  isl_set_free(set);
  return 0;
}

// Dependency analysis Func for multi-D access
int dep_analysis(isl_map * dep, int must, void * dep_user, void * user){
  
  //acc_info * acc_wr = (acc_info *)dep_user;
  stmt_info * stmt = (stmt_info *)user;

  std::cout << "DDDDDDDDD" << std::endl;
  isl_map_dump(dep);

  // sink affine
  isl_pw_multi_aff * snk = isl_pw_multi_aff_from_map(dep);
  //isl_pw_aff * snk = isl_pw_multi_aff_get_pw_aff(pwm_aff, 0);
  isl_pw_multi_aff_dump(snk);
  //isl_pw_multi_aff_free(pwm_aff);

  // statement domain
  isl_set_dump(stmt->domain);

  // source affine
  isl_space * sp = isl_set_get_space(isl_set_copy(stmt->domain));
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
  int success = isl_pw_multi_aff_foreach_piece(snk, check_multi_aff_diff, stmt);
  
  std::cout << "DDDDDDDDD" << std::endl;

  //isl_set_dump(stmt->param);
  isl_pw_multi_aff_free(snk);
  isl_aff_list_free(stmt->src);
  return 0;

}


/*
 * User defined Scop Modification
 */  
isl_set * analyzeScop(pet_scop * scop, VarMap * vm){
 
  std::cout << "********Scop Analysis Start**********" << std::endl;
  pet_scop_dump(scop);
  std::cout << "###########" << std::endl;

  // statement info
  // single statement for now!!!!!!!!!
  if(isl_set_is_empty(scop->stmts[0]->domain)){
    std::cout << "Empty Scop Domain, Check the correctness of the original code" << std::endl;   
    assert(false);
  }
  stmt_info stmt;
  stmt.scop = scop;
  stmt.domain = isl_set_copy(scop->stmts[0]->domain);
  stmt.context = isl_set_copy(scop->context);
  stmt.param = NULL;
  int s1 = pet_tree_foreach_access_expr(scop->stmts[0]->body, acc_expr_info, &stmt);  
  if (s1 == -1){
    isl_set_free(stmt.domain);
    isl_set_free(stmt.context);
    return NULL;
  }
  
  // isl_map_dump(scop->stmts[0]->schedule);

  // set up write containers
  acc_info acc_wr[stmt.n_acc_wr];
  int pt_coeff_wr[stmt.n_acc_wr][stmt.n_pt];
  int it_coeff_wr[stmt.n_acc_wr][stmt.n_it];
  for(int i=0; i<stmt.n_acc_wr; i++){
    acc_wr[i].pt_coeff = &pt_coeff_wr[i][0];
    acc_wr[i].it_coeff = &it_coeff_wr[i][0];    
  }  
  stmt.acc_wr = acc_wr;

  // set up read containers
  acc_info acc_rd[stmt.n_acc_rd];
  int pt_coeff_rd[stmt.n_acc_rd][stmt.n_pt];
  int it_coeff_rd[stmt.n_acc_rd][stmt.n_it];
  for(int i=0; i<stmt.n_acc_rd; i++){
    acc_rd[i].pt_coeff = &pt_coeff_rd[i][0];
    acc_rd[i].it_coeff = &it_coeff_rd[i][0];
  }  
  stmt.acc_rd = acc_rd;
 
  // scan expression
  stmt.n_acc_wr = 0;
  stmt.n_acc_rd = 0;
  int s2 = pet_tree_foreach_access_expr(scop->stmts[0]->body, acc_expr_scan, &stmt);

  if (s2 == -1){
    isl_set_free(stmt.domain);
    isl_set_free(stmt.context);
    return NULL;
  } 
  
  //analyze parameter range
  // S-Wr S/M-Rd
  isl_access_info * access;
  isl_flow * flow;
  int s3;
  for(int i=0; i<stmt.n_acc_rd; i++){
    // check name, only analysis array access with same name
    if(strcmp(acc_rd[i].name, acc_wr[0].name) != 0){
      continue;
    }
    std::cout << "***read access: "<< i << std::endl;

    // record which read access
    stmt.rd_pos = i;

    // create access info for one read access (sink)
    access = isl_access_info_alloc(isl_map_copy(acc_rd[i].map), &(acc_rd[i]), acc_order, 1);
    // add write access (source)
    access = isl_access_info_add_source(access, isl_map_copy(acc_wr[0].map), 1, &(acc_wr[0]));

    // compute flow
    flow = isl_access_info_compute_flow(access); 
    
    // analyze flow
    s3 = isl_flow_foreach(flow, dep_analysis, &stmt);
    
    // check whether there is no_source relation
    isl_map * no_src = isl_flow_get_no_source(flow, 1);
    if(isl_map_is_empty(no_src) !=1){
      if(stmt.param == NULL){
	stmt.param = isl_set_universe(isl_set_get_space(stmt.context));
      }
      else{
	stmt.param = isl_set_intersect(stmt.param, isl_set_universe(isl_set_get_space(stmt.context)));
      }
    }
    isl_map_free(no_src);
    
    // free isl_flow
    isl_flow_free(flow);
    std::cout << "*** " << s3 <<std::endl;
  }
  
  // isl_map * dep_non = isl_flow_get_no_source(flow, 1);
  // isl_map_dump(dep_non);
  std::cout << "********Scop Analysis End*********" << std::endl; 
  
  for(int i=0; i<stmt.n_acc_wr; i++){
    // record array name
    if(vm->find(acc_wr[i].name) == vm->end()){
      vm->insert(std::pair<std::string, std::string>(acc_wr[i].name, "int *"));
    }
    // clear isl related objects
    isl_map_free(acc_wr[i].map);
    isl_aff_free(acc_wr[i].aff);    
  }  

  for(int i=0; i<stmt.n_acc_rd; i++){
    // record array name
    if(vm->find(acc_rd[i].name) == vm->end()){
      vm->insert(std::pair<std::string, std::string>(acc_rd[i].name, "int *"));
    }
    // clear isl related object
    isl_map_free(acc_rd[i].map);
    isl_aff_free(acc_rd[i].aff);
  }

  isl_set_free(stmt.domain);
  isl_set_free(stmt.context);
  //isl_flow_free(flow);
  //isl_set_dump(stmt.param);
  return stmt.param;

}

  // Failed Approach
  // dep = isl_map_intersect_domain(dep, isl_set_copy(stmt->domain));
  // int exact = 0;
  // isl_map * len = isl_map_reaching_path_lengths(isl_map_copy(dep), &exact);
  // std::cout << "exact: " << exact << std::endl;
  // isl_map_dump(len);
  // len = isl_map_lexmax(len);
  // isl_map_dump(len);  
  // isl_pw_multi_aff * pwm_len = isl_pw_multi_aff_from_map(len);
  // isl_pw_aff * pw_len = isl_pw_multi_aff_get_pw_aff(pwm_len, 0);
  // isl_pw_aff_dump(pw_len);
  //assert(false);

  // S-Wr S-Rd
  //isl_map_dump(acc_rd[0].map);
  // isl_access_info * access = isl_access_info_alloc(isl_map_copy(acc_rd[0].map), &(acc_rd[0]), acc_order, 1);
  // access = isl_access_info_add_source(access, isl_map_copy(acc_wr[0].map), 1, &(acc_wr[0]));

  // isl_flow * flow = isl_access_info_compute_flow(access); 
 
  // int s3 = isl_flow_foreach(flow, dep_analysis, &stmt);

/*
// check 1-D access affine difference
int check_aff_diff(isl_set * set, isl_aff * aff, void * user){
  
  stmt_info * args = (stmt_info *)user;

  // src-snk + L-1 >=0
  // affine: source-sink = -distance
  isl_aff * diff = isl_aff_sub(isl_aff_copy(args->src), isl_aff_copy(aff)); 
  isl_aff_dump(diff);
  isl_constraint * cst = isl_inequality_from_aff(diff); 
  // constant += L-1, L is delay cycles, which is >=1 !!!!!!!!!!!!!!!!
  isl_val * c_val = isl_constraint_get_constant_val(cst);
  int c_num = isl_val_get_num_si(c_val);
  isl_val_free(c_val);
  cst = isl_constraint_set_constant_si(cst, c_num + L_delay -1 );
  isl_constraint_dump(cst);
  isl_set * cst_ub = isl_set_from_basic_set(isl_basic_set_from_constraint(cst));

  // snk-src -1 >=0
  // affine: sink-source = distance
  diff = isl_aff_sub(isl_aff_copy(aff), isl_aff_copy(args->src));
  cst = isl_inequality_from_aff(diff);
  // constant += -1
  c_val = isl_constraint_get_constant_val(cst);
  c_num = isl_val_get_num_si(c_val);
  isl_val_free(c_val);
  cst = isl_constraint_set_constant_si(cst, c_num -1 );
  isl_constraint_dump(cst);  
  isl_set * cst_lb = isl_set_from_basic_set(isl_basic_set_from_constraint(cst));  

  // intersect lower and upper bounds
  isl_set * bd = isl_set_intersect(cst_lb, cst_ub);
  isl_set_dump(bd);
  bd = isl_set_intersect(isl_set_copy(args->domain), bd);
  isl_set_dump(bd);

  // ** check emptiness for whether further check parameters
  isl_set * empty;
  bd = isl_set_partial_lexmax(bd, isl_set_copy(args->context), &empty);
  isl_set_dump(bd);
  isl_set_dump(empty);

  if(args->param == NULL){
    args->param = isl_set_copy(empty);
  }
  else{
    args->param = isl_set_intersect(args->param,isl_set_copy(empty));
  }
  //args->param = isl_set_params(*empty);

  //isl_set_dump(args->param); 
  isl_set_free(empty);
  isl_set_free(bd);
  isl_set_free(set);
  isl_aff_free(aff);
  return 0;
}

// Dependency analysis Func for 1-D access
int dep_analysis(isl_map * dep, int must, void * dep_user, void * user){
  
  //acc_info * acc_wr = (acc_info *)dep_user;
  stmt_info * stmt = (stmt_info *)user;

  std::cout << "DDDDDDDDD" << std::endl;
  isl_map_dump(dep);

  // sink affine
  isl_pw_multi_aff * snk = isl_pw_multi_aff_from_map(dep);
  isl_pw_aff * snk = isl_pw_multi_aff_get_pw_aff(pwm_aff, 0);
  isl_pw_multi_aff_dump(snk);
  isl_pw_multi_aff_free(pwm_aff);

  // statement domain
  isl_set_dump(stmt->domain);

  // source affine
  isl_space * sp = isl_set_get_space(isl_set_copy(stmt->domain));
  isl_local_space * lsp = isl_local_space_from_space(sp);
  stmt->src = isl_aff_var_on_domain(lsp, isl_dim_set, 0);
  isl_aff_dump(stmt->src);

  // distance between source and sink
  int success = isl_pw_multi_aff_foreach_piece(snk, check_aff_diff, stmt);
  
  std::cout << "DDDDDDDDD" << std::endl;

  //isl_set_dump(stmt->param);
  isl_pw_multi_aff_free(snk);
  isl_aff_free(stmt->src);
  return 0;

}

*/

