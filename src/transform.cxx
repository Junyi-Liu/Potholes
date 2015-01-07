#include <potholes/transform.h>
#include <potholes/affine.h>

#include <string>
#include <iostream>
#include <fstream>
#include <sstream>

#include </Users/Junyi/research/HLS/pet/expr.h>

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
  //isl_pw_aff_dump(max_pwaff);
  //isl_pw_aff_dump(min_pwaff);
  
  isl_pw_aff * dist_pwaff = isl_pw_aff_sub(max_pwaff, min_pwaff);
  isl_pw_aff_dump(dist_pwaff);

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
    bd = isl_set_partial_lexmax(bd, isl_set_universe(isl_set_get_space(stmt->context)), &empty);  // start from universal set
    isl_set_dump(bd);
    isl_set_dump(empty);
  }

  // add results
  std::cout << "** Adding result" << std::endl;
  if(stmt->param == NULL){
    stmt->param = isl_set_copy(empty);
  }
  else{
    // set_intersect for difference pieces(conditions), since current piece's safe range contains other piece's conflict range
    stmt->param = isl_set_intersect(stmt->param,isl_set_copy(empty));
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
 * User defined Scop Modification
 */  
isl_set * analyzeScop(pet_scop * scop, VarMap * vm){

  std::cout << "###########" << std::endl; 
  pet_scop_dump(scop);
  std::cout << "###########" << std::endl;

  // Record array access name and type
  for (int j = 0 ; j < scop->n_array  ; j++ ) {
    std::string element_type = scop->arrays[j]->element_type;    
    std::string pname = isl_set_get_tuple_name(scop->arrays[j]->extent);
    std::string ptype = element_type + std::string("*");   
    vm->insert(std::pair<std::string, std::string>(pname, ptype));        
  }

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
      return NULL;
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
      return NULL;
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
  std::cout << "********Scop Analysis Start**********" << std::endl;
  // S/M-Wr S/M-Rd
  // Current: consider all Wr-Rd access pairs with same array name !!!!!!!!!
  isl_access_info * access;
  isl_flow * flow;
  int s3;
  for(int j = 0; j<stmt.n_acc_wr; j++){
    std::cout << "======= Start write access: "<< j << "========"<< std::endl;
    
    // assign corresponding write access domain
    stmt.domain = isl_set_copy(scop->stmts[acc_wr[j].idx_stmt]->domain);    
    
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
  // Coalescing
  std::cout << "* Coalescing param " << std::endl;   
  stmt.param = isl_set_coalesce(stmt.param);
  isl_set_dump(stmt.param);
  //stmt.param = isl_set_detect_equalities(stmt.param);

  // isl_map * dep_non = isl_flow_get_no_source(flow, 1);
  // isl_map_dump(dep_non);
  std::cout << "********Scop Analysis End*********" << std::endl; 

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
