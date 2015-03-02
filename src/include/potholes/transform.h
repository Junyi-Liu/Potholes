/* 
 * File:   transform.h
 * Author: sb1708
 *
 * Created on October 21, 2013, 4:53 PM
 */

#ifndef TRANSFORM_H
#define	TRANSFORM_H

#include <potholes/analysis.h>
#include <potholes/rewrite.h>
#include <potholes/consumer.h>

namespace potholes { 

  class Transform : public potholes::Consumer, potholes::Rewriter { 

  public:
    Analysis& analysis;
    // applied to particular scop
    // specific function for consumer initialization
        
    // specific function for rewrite callback (makes changes to rewrite tree in analysis
        
    virtual void Initialize(clang::ASTContext& Context) = 0;
    virtual bool HandleTopLevelDecl(clang::DeclGroupRef d) = 0;
    virtual void ApplyTransformation(clang::Rewriter&) = 0;
        
    Transform(Analysis&);

  };
    
  class PromoteScop : public Transform { 
    
  public:
    PromoteScop(Analysis&);
    virtual void Initialize(clang::ASTContext& Context);
    virtual bool HandleTopLevelDecl(clang::DeclGroupRef d);
    virtual void ApplyTransformation(clang::Rewriter&);
        
  private:
    void removeScop(clang::Rewriter&);
    void insertScop(clang::Rewriter&);       
        
  };
    
}

/*
 * SCoP Analysis 
 */
//#define L_delay 25 // dummy statement delay
#define delay_info_path "/Users/Junyi/research/HLS/application/vivado_play/loop_info/delay.dat"

struct acc_info {
  
  // array name
  const char * name;

  // line number
  //int line;

  // mother statement index
  int idx_stmt;

  // access pattern map
  isl_map * map;

  // affine
  //isl_aff * aff;

  // parameters (uncertain variable)
  int n_pt;
  //int *pt_coeff;
  
  // iterators
  int n_it;
  //int *it_coeff;

  // constant
  //int cnt;
      
};
typedef struct acc_info acc_info;

struct stmt_info{
  
  pet_scop * scop;

  isl_aff_list * src;

  // current statement index
  int idx;
  // current src statement domain
  isl_set * domain;
  // current snk statement domain
  isl_set * dom_snk;
  
  // scop context
  isl_set * context;

  // current paramter safe region
  isl_set * param;

  // current iteration conflict region
  isl_set * cft;
  
  // statement memeory access info
  int n_acc_wr = 0; 
  acc_info *acc_wr; 
  int n_acc_rd = 0; 
  acc_info *acc_rd; 

  /* int n_acc = 0; */
  /* acc_info *acc; */
  
  int rd_pos;

  int n_pt;
  int n_it;  

  // delay info
  int L_delay;    
  
  // best Initial Interval
  int II;

};
typedef struct stmt_info stmt_info;

struct recur_info{

  // paramter safe region
  isl_set * param = NULL;
  
  // iteration conflict region
  isl_set * cft = NULL;
  
};
typedef struct recur_info recur_info;  

int aff_scan(isl_set *set, isl_aff *aff, void *user);
int acc_expr_scan(pet_expr *expr, void *user);
int acc_expr_info(pet_expr *expr, void *user);
int acc_order(void * first, void * second);
int check_aff_diff(isl_set * set, isl_aff * aff, void * user);
int dep_analysis(isl_map * dep, int must, void * dep_user, void * user);

//User defined SCoP analysis
void analyzeScop(pet_scop * scop, VarMap * vm, VarMap * tm, recur_info * rlt); 

//User defined SCoP Modification
void splitLoop(pet_scop * scop, __isl_keep isl_set * cft);


#endif	/* TRANSFORM_H */

