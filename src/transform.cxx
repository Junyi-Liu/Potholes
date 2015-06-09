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
    std::cout << "###cannot analyze wrapped access" << std::endl;
    return -1;
  }

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
int get_aff_plus_1(__isl_take isl_set * set, __isl_take isl_aff * aff, void * user ){

  isl_aff ** dist_aff = (isl_aff **)user;
  
  if( *dist_aff == NULL ){
    *dist_aff = isl_aff_copy(aff);
    isl_aff_dump(*dist_aff);
  }

  isl_aff_free(aff);
  isl_set_free(set);
  return 0;
}

// Get the size of the dimention of a given isl_set
isl_aff * get_dim_size(__isl_keep isl_set * set, unsigned dim){

  isl_pw_aff * max_pwaff = isl_set_dim_max(isl_set_copy(set), dim);
  isl_pw_aff * min_pwaff = isl_set_dim_min(isl_set_copy(set), dim);
  isl_pw_aff_dump(max_pwaff);
  isl_pw_aff_dump(min_pwaff);
  
  isl_pw_aff * dist_pwaff = isl_pw_aff_sub(max_pwaff, min_pwaff);
  isl_pw_aff_dump(dist_pwaff);

  isl_set_dump(set);
  //assert(false);
  
  isl_aff * dist_aff = NULL;  
  int success = isl_pw_aff_foreach_piece(dist_pwaff, get_aff_plus_1, &dist_aff);
  isl_aff_dump(dist_aff);


  isl_space * sp = isl_set_get_space(set);
  isl_aff * rtn_aff = isl_aff_zero_on_domain(isl_local_space_from_space(sp));
  
  // copy distance affine to the proper domain space
  rtn_aff = isl_aff_set_constant_val(rtn_aff, isl_aff_get_constant_val(dist_aff));
  for(int i = 0; i< isl_aff_dim(rtn_aff, isl_dim_param); i++){
    rtn_aff = isl_aff_set_coefficient_val(rtn_aff, isl_dim_param, i, isl_aff_get_coefficient_val(dist_aff, isl_dim_param, i));
  }
  isl_aff_dump(rtn_aff);

  isl_pw_aff_free(dist_pwaff);
  isl_aff_free(dist_aff);
  return isl_aff_add_constant_si(rtn_aff, 1); //max-min+1
}

// check multi-affine difference
int check_multi_aff_diff(isl_set * set, isl_multi_aff * maff, void * user){

  stmt_info * stmt = (stmt_info *)user;

  std::cout << "=== current piece set: "<< std::endl;
  isl_set_dump(set);
  //assert(false);

  // (src-snk) in multi-afffine
  for(int i=0; i<stmt->n_it; i++){
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
  // isl_space * sp = isl_set_get_space(isl_set_copy(stmt->domain));
  isl_space * sp = isl_multi_aff_get_domain_space(maff);
  isl_local_space * lsp = isl_local_space_from_space(sp);
  isl_ctx * ctx = isl_local_space_get_ctx(lsp);
  isl_val * val_one = isl_val_one(ctx);
  isl_aff * ftr = isl_aff_val_on_domain(isl_local_space_copy(lsp), val_one);
  isl_aff * diff = isl_aff_zero_on_domain(isl_local_space_copy(lsp));
  for(int i=stmt->n_it-1; i>=0; i--){
    std::cout << "* dimension: "<< i << std::endl;
    // add dimension item with factor
    isl_aff * dim = isl_multi_aff_get_aff(maff, i);
    dim = isl_aff_mul(dim, isl_aff_copy(ftr));
    diff = isl_aff_add(diff, dim);    
    // scale up factor
    // consider paramterized dim bounds
    if(i>0){
      ftr = isl_aff_mul(ftr, get_dim_size(stmt->domain, i));
      isl_aff_dump(ftr);
    }
  }
  std::cout << "* flattened (src-snk): "<< std::endl;
  isl_aff_dump(diff);
  isl_aff_free(ftr);  
  //isl_ctx_free(ctx);
  
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
  // when statement schedule dimension numbers are different ???????? 
  bd = isl_set_reset_tuple_id(bd);
  std::cout << "** Adding result" << std::endl;
  // if(stmt->param == NULL){
  //   stmt->param = isl_set_copy(empty);
  //   stmt->cft = isl_set_copy(bd);
  // }
  // else{
  //   // set_intersect for difference pieces(conditions), since current piece's safe range contains other piece's conflict range
  //   stmt->param = isl_set_intersect(stmt->param,isl_set_copy(empty));
  //   stmt->cft = isl_set_union(stmt->cft, isl_set_copy(bd));
  // }

  if(isl_set_is_empty(bd) != 1){
    // set_intersect for difference pieces(conditions), since current piece's safe range contains other piece's conflict range
    stmt->param = isl_set_intersect(stmt->param,isl_set_copy(empty));
    stmt->cft = isl_set_union(stmt->cft, isl_set_copy(bd));
  }
  
  //stmt->param = isl_set_params(*empty);

  //assert(false);

  isl_set_dump(stmt->param); 

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
  stmt.L_delay = ceil(float(stmt.L_delay)/float(stmt.II));
  std::cout<< "*** Ceil( Delay/II ): " << stmt.L_delay << std::endl;  

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

    std::cout << "==== Schedule: " << std::endl;
    isl_map_dump(scop->stmts[acc_wr[j].idx_stmt]->schedule);

    //record number of pt and it
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
  //stmt.param = isl_set_detect_equalities(stmt.param);

  // isl_map * dep_non = isl_flow_get_no_source(flow, 1);
  // isl_map_dump(dep_non);
  std::cout << "***************** SCOP ANALYSIS END *******************" << std::endl; 

  // copy final results
  rlt->param = isl_set_copy(stmt.param);
  rlt->cft = isl_set_copy(stmt.cft);
  
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


int inc_dim(__isl_take isl_constraint * c, void * user){

  sch_info * sch = (sch_info *) user; 
  
  //isl_constraint_dump(c);
  if(isl_constraint_involves_dims(c, isl_dim_out, sch->d * 2, 1)){
    isl_val * val = isl_constraint_get_constant_val(c);
    val = isl_val_sub_ui(val, sch->i); //output dim plus 1
    c = isl_constraint_set_constant_val(c, val);
    sch->bmap = isl_basic_map_add_constraint(sch->bmap, isl_constraint_copy(c));
  }  
  
  isl_constraint_free(c);
  return 0;
}


int modify_schedule(__isl_take isl_basic_map * bmap, void * user){

  sch_info * sch = (sch_info *) user;

  sch->bmap = isl_basic_map_copy(bmap); 
  sch->bmap = isl_basic_map_drop_constraints_involving_dims(sch->bmap, isl_dim_out, sch->d * 2, 1);
  
  int s1 = isl_basic_map_foreach_constraint(bmap, inc_dim, sch);

  sch->sch_map = isl_map_from_basic_map(sch->bmap);
  
  isl_basic_map_free(bmap); 
  return 0;
}


int change_stmt_id(__isl_keep pet_expr *expr, void *user){

  isl_id * p_id = (isl_id *) user;

  isl_map * acc_map = pet_expr_access_get_access(expr);
  acc_map = isl_map_set_tuple_id(acc_map, isl_dim_in, isl_id_copy(p_id));
  expr = pet_expr_access_set_access(expr, acc_map);
  
  return 0;
}

// check whether the specific dimension of the set is single-valued
int check_dim_single(__isl_keep isl_set * dom, int pos){
  isl_pw_aff * dim_min = isl_set_dim_min(isl_set_copy(dom), pos); 
  isl_pw_aff * dim_max = isl_set_dim_max(isl_set_copy(dom), pos);
  int ds = isl_pw_aff_is_equal(dim_min, dim_max);
  isl_pw_aff_free(dim_min);
  isl_pw_aff_free(dim_max);
  //std::cout << "*** dom splitted dim is single-valued: " << ds << std::endl;
  return ds;
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

// for schedule map splitting
__isl_give isl_map * sch_inc(__isl_keep isl_map * stmt_sch, __isl_keep isl_set * dom, __isl_keep isl_id * stmt_id, int pos, int i){
  // ?? Problem: scheduling map does not make the loop generated as its tree structre
  // ?? Currently just use same schedule map for the splitted inner loops 
  sch_info sch;
  sch.d = pos;
  sch.i = i;
  int s1 = isl_map_foreach_basic_map(stmt_sch, modify_schedule, &sch);
  sch.sch_map = isl_map_set_tuple_id(sch.sch_map, isl_dim_in, isl_id_copy(stmt_id));  
  return isl_map_intersect_domain(sch.sch_map, isl_set_copy(dom));
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


/*
 * User defined Scop Modification
 */
int splitLoop(pet_scop * scop, recur_info * rlt){

  // Show Conflict Region 
  std::cout << "==== Conflict Region: " << std::endl; 
  isl_set_dump(rlt->cft);
  std::cout << "==== lexmin point: " << std::endl;   
  isl_set * pnt_lexmin = isl_set_lexmin(isl_set_copy(rlt->cft));
  isl_set_dump(pnt_lexmin); 
  std::cout << "==== lexmax point: " << std::endl;     
  isl_set * pnt_lexmax = isl_set_lexmax(isl_set_copy(rlt->cft));
  isl_set_dump(pnt_lexmax);

  // dimension number of conflict set
  int n_cd = isl_set_dim(rlt->cft, isl_dim_set);
  
  //assert(false);
  
  // statement information
  std::cout << "==== Number of statements in SCoP: "<< scop->n_stmt << std::endl;
  int n_stmt = scop->n_stmt;
  isl_set * stmt_dom_rcd[n_stmt]; //statement domain record

  for(int i_st=0; i_st < n_stmt; i_st++){
    //int i_st = 0;

    std::cout << "\n==================== Start statement in SCoP: "<< i_st << " ===================" << std::endl;

    // Copy statement domain
    isl_set * stmt_dom = isl_set_copy(scop->stmts[i_st]->domain);
    stmt_dom_rcd[i_st] = isl_set_copy(stmt_dom);
    stmt_dom = isl_set_reset_tuple_id(stmt_dom);
    std::cout << "==== Statement domain: " << std::endl;
    isl_set_dump(stmt_dom);

    // Copy statement schedule
    isl_map * stmt_sch = isl_map_copy(scop->stmts[i_st]->schedule);

    // Detect which dimension to be splitted
    // more complex cases need for this part!
    int n_dd = isl_set_dim(stmt_dom, isl_dim_set);
    int n_d = (n_cd < n_dd) ? n_cd : n_dd;
    isl_pw_aff * cd_min;
    isl_pw_aff * cd_max;
    isl_pw_aff * dd_min;
    isl_pw_aff * dd_max;
    int eq_min, eq_max;
    int i_dim = -1;
    for(int i = n_d-1; i >= 0; i--){
      cd_min = isl_set_dim_min(isl_set_copy(pnt_lexmin), i); 
      dd_min = isl_set_dim_min(isl_set_copy(stmt_dom), i);
      cd_max = isl_set_dim_max(isl_set_copy(pnt_lexmax), i); 
      dd_max = isl_set_dim_max(isl_set_copy(stmt_dom), i);
      eq_min = isl_pw_aff_is_equal(cd_min, dd_min); 
      eq_max = isl_pw_aff_is_equal(cd_max, dd_max);
      isl_pw_aff_free(cd_min);
      isl_pw_aff_free(cd_max);
      isl_pw_aff_free(dd_min);
      isl_pw_aff_free(dd_max);
      if(eq_min == 0 || eq_max == 0){
	i_dim = i;
	break;
      }
    }
    std::cout << "==== Dimension to be splitted: " << i_dim << std::endl;

    // Cut inner most loop bounds by the LEXMAX point
    std::cout << "\n======= Start domain cut by lexmax of conflict region =======" << std::endl;
    cst_info info;
    info.i_dim = i_dim;
    info.stmt_dom = isl_set_copy(stmt_dom);
    //info.new_dom = isl_set_copy(stmt_dom);
    info.n_bst = 0;
    int s1 = isl_set_foreach_basic_set(pnt_lexmax, constraint_scan, &info);
    isl_set * dom_lexmax = isl_set_copy(info.new_dom);
    std::cout << "======= End domain cut by lexmax of conflict region =======" << std::endl;
    isl_set_dump(dom_lexmax);
    isl_set_free(info.new_dom);

    // Cut inner most loop bounds by the LEXMIN point
    std::cout << "\n======= Start domain cut by lexmin of conflict region ======" << std::endl;
    //info.new_dom = isl_set_copy(stmt_dom);
    info.n_bst = 0;
    s1 = isl_set_foreach_basic_set(pnt_lexmin, constraint_scan, &info);
    isl_set * dom_lexmin = isl_set_copy(info.new_dom);
    std::cout << "======= End domain cut by lexmin of conflict region ======" << std::endl;
    isl_set_dump(dom_lexmin);
    isl_set_free(info.new_dom);
    isl_set_free(info.stmt_dom);

    // check whether splitted dim is single valued
    int ds_lexmin = check_dim_single(dom_lexmin, i_dim);
    

    // Set Subtraction
    std::cout << "\n======= Domain Subtraction  ======" << std::endl;
    // Part 3
    std::cout << "*** Part 3: " << std::endl;
    // isl_set * dom_3 = isl_set_intersect_params(isl_set_copy(stmt_dom), isl_set_complement(isl_set_copy(rlt->param)));
    // dom_3 = isl_set_subtract(dom_3, isl_set_copy(dom_lexmax));
    isl_set * dom_3 = isl_set_subtract(isl_set_copy(stmt_dom), isl_set_copy(dom_lexmax));
    //isl_set_dump(dom_3);

    // check whether splitted dim is single valued
    int ds_3 = check_dim_single(dom_3, i_dim);
    if(ds_3 == 1){
      isl_set_free(dom_3);
      dom_3 = isl_set_empty(isl_set_get_space(stmt_dom));
    }    

    //dom_3 = isl_set_intersect_params(dom_3, isl_set_complement(isl_set_copy(rlt->param)));
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
  
    //dom_2 = isl_set_intersect_params(dom_2, isl_set_complement(isl_set_copy(rlt->param)));
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
  
    //dom_1 = isl_set_intersect_params(dom_1, isl_set_complement(isl_set_copy(rlt->param)));
    isl_set_dump(dom_1);

    // Special Case: dom_1 and dom_3 are all empty
    int n_bs_1 = isl_set_n_basic_set(dom_1);
    int n_bs_2 = isl_set_n_basic_set(dom_2);
    int n_bs_3 = isl_set_n_basic_set(dom_3);
    int n_bs = n_bs_1 + n_bs_2 + n_bs_3;
    std::cout << "*** Sum of bset number : "<< n_bs << std::endl;
    
    int t = 0;
    if(n_bs_1 > 3 || n_bs_2 > 3 || n_bs_3 > 3){
      //if(n_bs_1 > 4){
      std::cout << "==== Too many basic sets for loop splitting" << std::endl;
      t = 1;
    }
    if(ds_lexmin == 1 && ds_3 == 1){
      std::cout << "==== Part 1 and Part 3 are all empty: Apply parametric loop pipelining" << std::endl;
      t = 1;
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

    //Special Case: dom_1 or dom_3 are not fully single
    if(ds_lexmin != 1 || ds_3 != 1){
      std::cout << "*** Seperate single basic sets of dom_1 and dom_3" << std::endl;
      dom_sep sep;
      sep.i_dim = i_dim;

      sep.s = 0;
      sep.dom_n = isl_set_empty(isl_set_get_space(stmt_dom));
      sep.dom_s = isl_set_empty(isl_set_get_space(stmt_dom));
      s1 = isl_set_foreach_basic_set(dom_1, seperate_singles, &sep);
      if(sep.s){
	isl_set_free(dom_1);
	dom_1 = isl_set_copy(sep.dom_n);
	dom_2 = isl_set_union(dom_2, sep.dom_s);
	isl_set_free(sep.dom_n);
	dom_1 = isl_set_remove_redundancies(dom_1);
	dom_1 = isl_set_coalesce(dom_1);
	dom_2 = isl_set_remove_redundancies(dom_2);
	dom_2 = isl_set_coalesce(dom_2);
      }

      sep.s = 0;
      sep.dom_n = isl_set_empty(isl_set_get_space(stmt_dom));
      sep.dom_s = isl_set_empty(isl_set_get_space(stmt_dom));
      s1 = isl_set_foreach_basic_set(dom_3, seperate_singles, &sep);
      if(sep.s){
	isl_set_free(dom_3);
	dom_3 = isl_set_copy(sep.dom_n);
	dom_2 = isl_set_union(dom_2, sep.dom_s);
	isl_set_free(sep.dom_n);
	dom_3 = isl_set_remove_redundancies(dom_3);
	dom_3 = isl_set_coalesce(dom_3);
	dom_2 = isl_set_remove_redundancies(dom_2);
	dom_2 = isl_set_coalesce(dom_2);
      }      
    }
    
    // remove conflict region related parameter constraints
    //dom_3 = remove_param_cft(dom_3, rlt->param);
    //dom_2 = remove_param_cft(dom_2, rlt->param);
    //dom_1 = remove_param_cft(dom_1, rlt->param);
    std::cout << "\n*** Dom 1: " << std::endl;
    isl_set_dump(dom_1);
    std::cout << "*** Dom 2: " << std::endl;
    isl_set_dump(dom_2);
    std::cout << "*** Dom 3: " << std::endl;
    isl_set_dump(dom_3);
    
    //assert(false);
  
    // Modify SCoP
    std::cout << "\n================= Modify SCoP =================" << std::endl;
    int ui_st = scop->n_stmt;
    scop->n_stmt = scop->n_stmt + 2;
    
    isl_ctx * ctx = pet_tree_get_ctx(scop->stmts[i_st]->body);
    scop->stmts = isl_realloc(ctx, scop->stmts, struct pet_stmt *, sizeof(struct pet_stmt *) * scop->n_stmt);

    // Part 1
    std::cout << "\n======= Part 1 " << std::endl;
    std::cout << "*** Domain: " << std::endl;
    isl_id * stmt_id = isl_set_get_tuple_id(scop->stmts[i_st]->domain);    
    dom_1 = isl_set_set_tuple_id(dom_1, isl_id_copy(stmt_id));
    isl_set_free(scop->stmts[i_st]->domain);
    scop->stmts[i_st]->domain = isl_set_copy(dom_1);
    isl_set_dump(scop->stmts[i_st]->domain);
    //isl_set_free(dom_2);
  
    std::cout << "*** Schedule: " << std::endl;
    scop->stmts[i_st]->schedule = sch_inc(stmt_sch, dom_1, stmt_id, i_dim, 1);
    isl_map_dump(scop->stmts[i_st]->schedule);
  
    // Part 2
    std::cout << "\n======= Part 2 " << std::endl;
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

    //assert(false);

    std::cout << "*** Domain: " << std::endl;
    // set specific id name for the first splitted stmt
    std::string p2_str;
    if(i_st == 0){
      p2_str.assign("p2");
    }
    else{
      p2_str.assign(isl_id_get_name(stmt_id));
      p2_str.append("_p2");
    }
    isl_id * p_id = isl_id_alloc(ctx, p2_str.c_str(), NULL);
    dom_2 = isl_set_set_tuple_id(dom_2, isl_id_copy(p_id));
    //dom_2 = isl_set_set_tuple_id(dom_2, isl_id_copy(stmt_id));
    scop->stmts[ui_st]->domain = isl_set_copy(dom_2);  
    isl_set_dump(scop->stmts[ui_st]->domain);

    std::cout << "*** Schedule: " << std::endl;
    scop->stmts[ui_st]->schedule = sch_inc(stmt_sch, dom_2, p_id, i_dim, 2);
    isl_map_dump(scop->stmts[ui_st]->schedule);

    std::cout << "*** Stmt body: " << std::endl;
    scop->stmts[ui_st]->body = pet_tree_copy(scop->stmts[i_st]->body);
    //s1 = pet_tree_foreach_access_expr(scop->stmts[ui_st]->body, change_stmt_id, p_id);
    isl_id_free(p_id);

    //assert(false);
  
    // Part 3
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
    if(i_st == 0){
      p3_str.assign("p3");
    }
    else{
      p3_str.assign(isl_id_get_name(stmt_id));
      p3_str.append("_p3");
    }
    p_id = isl_id_alloc(ctx, p3_str.c_str(), NULL);
    dom_3 = isl_set_set_tuple_id(dom_3, isl_id_copy(p_id));
    //dom_3 = isl_set_set_tuple_id(dom_3, isl_id_copy(stmt_id));
    scop->stmts[ui_st+1]->domain = isl_set_copy(dom_3);  
    isl_set_dump(scop->stmts[ui_st+1]->domain);

    std::cout << "*** Schedule: " << std::endl;
    scop->stmts[ui_st+1]->schedule = sch_inc(stmt_sch, dom_3, p_id, i_dim, 3);
    isl_map_dump(scop->stmts[ui_st+1]->schedule);

    std::cout << "*** Stmt body: " << std::endl;
    scop->stmts[ui_st+1]->body = pet_tree_copy(scop->stmts[i_st]->body);
    //s1 = pet_tree_foreach_access_expr(scop->stmts[ui_st+1]->body, change_stmt_id, p_id);
    isl_id_free(p_id);
    
  
    //assert(false);
    isl_id_free(stmt_id);
    isl_set_free(dom_3);
    isl_set_free(dom_2);
    isl_set_free(dom_1);
    isl_set_free(stmt_dom);  
    isl_map_free(stmt_sch);  
    isl_set_free(dom_lexmax);
    isl_set_free(dom_lexmin);

    //isl_ctx_free(ctx);
    std::cout << "==================== End statement in SCoP: "<< i_st << " ===================" << std::endl;
  }

  for(int i_st=0; i_st<n_stmt; i_st++){
    isl_set_free(stmt_dom_rcd[i_st]);
  }
  isl_set_free(pnt_lexmin);
  isl_set_free(pnt_lexmax);
  return 0;
}

