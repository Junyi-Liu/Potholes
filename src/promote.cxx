#include <potholes/transform.h>
#include <iostream>


/* class ScopRewriteConsumer : public clang::ASTConsumer {
   private:
   clang::Rewriter & rewriter;
   potholes::Analysis & extractor;



   public:

   ScopRewriteConsumer(clang::Rewriter& rewriter, potholes::Analysis & extractor) :
   clang::ASTConsumer(),
   rewriter(rewriter),
   extractor(extractor) {
   }
        
*/

potholes::PromoteScop::PromoteScop(potholes::Analysis& analysis) : potholes::Transform(analysis) {
    
}

void potholes::PromoteScop::Initialize(clang::ASTContext& Context) {


  std::cout << "Initialized Promotion Transformation" << "\n";

}

bool potholes::PromoteScop::HandleTopLevelDecl(clang::DeclGroupRef d) {
  // find legal places to put a function declaration
  // put comments there. 

  //  std::cout << "PromoteScop Handle Decl" << "\n";
  // static int count = 0;
  clang::DeclGroupRef::iterator it;
  for (it = d.begin(); it != d.end(); it++) {

    //clang::ASTContext & Context = (*it)->getASTContext();

    //  clang::SourceManager & sm = Context.getSourceManager();
    //    clang::SourceManager & am = rewriter.getSourceMgr();

    clang::SourceLocation FullLocation = (*it)->getLocStart();

    if (FullLocation.isValid()) {
      analysis.extractor.getLocations().addLocation(FullLocation);
    }
  }
  return true;
}

void potholes::PromoteScop::ApplyTransformation(clang::Rewriter& rewriter) {

  // Scop replacement
  removeScop(rewriter);

#ifdef LSP
  insertScop(rewriter);
#endif

  return;

}
         
void potholes::PromoteScop::removeScop(clang::Rewriter& rewriter) {
  std::vector<std::string>::iterator pit;

  // need to get paths from analysis object
            
  Analysis::Files paths = analysis.getSources();
            
  std::string function_name = "accelerated_scop";

  for (pit = paths.begin(); pit != paths.end(); pit++) {
    // std::cout << getAbsolutePath(*pit) << std::endl;
    potholes::Scop * scop = analysis.extractor.GetScop(getAbsolutePath(*pit));

    if (scop) {
      // pet_scop_dump(scop->scop);

      // ** Analyze Scop HERE !!!!!!!!!!
      // isl_set * param = NULL;
      //isl_set * param = analyzeScop(scop->scop);
      
      // get scop location information
      unsigned start = pet_loc_get_start(scop->scop->loc);
      unsigned finish = pet_loc_get_end(scop->scop->loc);
      //unsigned start = scop->scop->start;
      //unsigned finish = scop->scop->end;

      clang::SourceManager & sm = rewriter.getSourceMgr();
      clang::SourceManager::fileinfo_iterator fit;

      for (fit = sm.fileinfo_begin(); fit != sm.fileinfo_end(); fit++) {
	const clang::FileEntry * fe = fit->first;
                    
	if (fe) {
	  if (std::string(fe->getName()) == getAbsolutePath(*pit)) {

	    clang::SourceLocation file_start = sm.getLocForStartOfFile(sm.translateFile(fe));
	    clang::SourceLocation fs = file_start.getLocWithOffset(start);
	    clang::SourceLocation fe = file_start.getLocWithOffset(finish);

	    std::stringstream ss;

	    ss << pth_generate_scop_function_replace(scop->scop, function_name);
	    
	    //Junyi
	    rewriter.ReplaceText(clang::SourceRange(fs, fe), ss.str());

	  }
	}
      }

      // isl_set_free(param);     
      
    }
  }
  
  return;

}
                                 
         
void potholes::PromoteScop::insertScop(clang::Rewriter& rewriter) {
  Analysis::Files paths = analysis.getSources();
            
  std::vector<std::string>::iterator pit;
  for (pit = paths.begin(); pit != paths.end(); pit++) {
    
    //potholes::Scop * scop = analysis.extractor.GetScop(getAbsolutePath(*pit));
    clang::SourceManager & sm = rewriter.getSourceMgr();
    clang::SourceManager::fileinfo_iterator fit;
    
    for (fit = sm.fileinfo_begin(); fit != sm.fileinfo_end(); fit++) {
      const clang::FileEntry * fe = fit->first;

      if (fe) {
                   
	if (std::string(fe->getName()) == getAbsolutePath(*pit)) {
	  
	  // Find location to insert scop declaration
	  clang::SourceLocation insertLocation = analysis.extractor.find_insert_location(sm, getAbsolutePath(*pit));
	  // Inserts scop function declaration
  
	  std::stringstream  ss;
	  //ss << "/* Begin Accelerated Scop Definition */ \n";

	  std::string function_name = "accelerated_scop";

	  ss << "/* Begin Extra Functions Definition */ \n";
	  ss << "int min(int a, int b) { return (a<b) ? a : b;} \n";
	  ss << "int max(int a, int b) { return (a>b) ? a : b;} \n";
	  ss << "/* End Extra Functions Definition */ \n\n";
	  
	  //Junyi: Remove Declaration for inline transformation
	  //ss << pth_generate_scop_function_declaration(scop->scop, function_name) << "\n";
	  
	  //ss << "/* End Accelerated Scop Definition */ \n\n";
	  rewriter.InsertTextAfter(insertLocation, ss.str());
	  analysis.addAcceleratedFunction(getAbsolutePath(*pit), function_name);
	}
      }
    }
  }
  
  return;
}

// /*
//  * User defined Scop Modification
//  */  
// void potholes::PromoteScop::changeScop(pet_scop * scop){
 
//   std::cout << "***********Scop Transformation Start****************" << std::endl;
//   pet_scop_dump(scop);
//   std::cout << "=======================" << std::endl;
  
//   isl_set_dump(scop->context);

//   isl_id * p = isl_set_get_dim_id(scop->context, isl_dim_param, 0);
//   isl_id_dump(p);

//   std::cout << "***********Scop Transformation End****************" << std::endl;  

// }
