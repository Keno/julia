// clang state
#undef B0 //rom termios
#include "llvm/ADT/DenseMapInfo.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "clang/Sema/ScopeInfo.h"
#include "clang/AST/ASTContext.h"
#include "clang/Parse/Parser.h"
#include "clang/Parse/ParseDiagnostic.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Analysis/DomainSpecific/CocoaConventions.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Lex/HeaderSearch.h"
#include "clang/Parse/ParseAST.h"
#include "clang/Lex/Lexer.h"
#include "clang/Sema/Sema.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Sema/SemaDiagnostic.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Initialization.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSwitch.h"
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Frontend/CodeGenOptions.h>
#include <clang/AST/Type.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclTemplate.h>
#include <clang/Basic/Specifiers.h>
#include "CodeGen/CodeGenModule.h"
#include <CodeGen/CodeGenTypes.h>
#include <CodeGen/CodeGenFunction.h>

static clang::ASTContext *clang_astcontext;
static clang::CompilerInstance *clang_compiler;
static clang::CodeGen::CodeGenModule *clang_cgm;
static clang::CodeGen::CodeGenTypes *clang_cgt;
static clang::CodeGen::CodeGenFunction *clang_cgf;
static DataLayout *TD;

static llvm::Module *clang_shadow_module;

extern "C" {
  // clang types
  DLLEXPORT const clang::Type *cT_int1;
  DLLEXPORT const clang::Type *cT_int8;
  DLLEXPORT const clang::Type *cT_uint8;
  DLLEXPORT const clang::Type *cT_int16;
  DLLEXPORT const clang::Type *cT_uint16;
  DLLEXPORT const clang::Type *cT_int32;
  DLLEXPORT const clang::Type *cT_uint32;
  DLLEXPORT const clang::Type *cT_int64;
  DLLEXPORT const clang::Type *cT_uint64;
  DLLEXPORT const clang::Type *cT_char;
  DLLEXPORT const clang::Type *cT_size;
  DLLEXPORT const clang::Type *cT_int128;
  DLLEXPORT const clang::Type *cT_uint128;
  DLLEXPORT const clang::Type *cT_complex64;
  DLLEXPORT const clang::Type *cT_complex128;
  DLLEXPORT const clang::Type *cT_float32;
  DLLEXPORT const clang::Type *cT_float64;
  DLLEXPORT const clang::Type *cT_void;
  DLLEXPORT const clang::Type *cT_pvoid;
}

static bool in_cpp = false;

typedef struct cppcall_state {
    // Save previous globals
    llvm::Module *module;
    llvm::Function *func;
    llvm::Function *CurFn;
    llvm::BasicBlock *block;
    llvm::BasicBlock::iterator point;
    llvm::Instruction *prev_alloca_bb_ptr;
    // Current state
    llvm::Instruction *alloca_bb_ptr;
} cppcall_state_t;

class JuliaCodeGenerator : public clang::ASTConsumer {
  public:
    JuliaCodeGenerator() {}

    virtual ~JuliaCodeGenerator() {}

    virtual void HandleCXXStaticMemberVarInstantiation(clang::VarDecl *VD) {
      clang_cgm->HandleCXXStaticMemberVarInstantiation(VD);
    }

    virtual bool HandleTopLevelDecl(clang::DeclGroupRef DG) {
      // Make sure to emit all elements of a Decl.
      for (clang::DeclGroupRef::iterator I = DG.begin(), E = DG.end(); I != E; ++I)
        clang_cgm->EmitTopLevelDecl(*I);
      return true;
    }

    /// HandleTagDeclDefinition - This callback is invoked each time a TagDecl
    /// to (e.g. struct, union, enum, class) is completed. This allows the
    /// client hack on the type, which can occur at any point in the file
    /// (because these can be defined in declspecs).
    virtual void HandleTagDeclDefinition(clang::TagDecl *D) {
      clang_cgm->UpdateCompletedType(D);
      
      // In C++, we may have member functions that need to be emitted at this 
      // point.
      if (clang_astcontext->getLangOpts().CPlusPlus && !D->isDependentContext()) {
        for (clang::DeclContext::decl_iterator M = D->decls_begin(), 
                                     MEnd = D->decls_end();
             M != MEnd; ++M)
          if (clang::CXXMethodDecl *Method = dyn_cast<clang::CXXMethodDecl>(*M))
            if (Method->doesThisDeclarationHaveABody() &&
                (Method->hasAttr<clang::UsedAttr>() || 
                 Method->hasAttr<clang::ConstructorAttr>()))
              clang_cgm->EmitTopLevelDecl(Method);
      }
    }

    virtual void CompleteTentativeDefinition(clang::VarDecl *D) {
      clang_cgm->EmitTentativeDefinition(D);
    }

    virtual void HandleVTable(clang::CXXRecordDecl *RD, bool DefinitionRequired) {
      clang_cgm->EmitVTable(RD, DefinitionRequired);
    }
};

struct FooBar {
  void *CIdx;
  clang::ASTUnit *TheASTUnit;
  void *StringPool;
  void *Diagnostics;
  void *OverridenCursorsPool;
  void *FormatContext;
  unsigned FormatInMemoryUniqueId;
};


extern "C" {

void myParseAST(clang::Sema &S, bool PrintStats, bool SkipFunctionBodies) {
  // Collect global stats on Decls/Stmts (until we have a module streamer).
  if (PrintStats) {
    clang::Decl::EnableStatistics();
    clang::Stmt::EnableStatistics();
  }

  // Also turn on collection of stats inside of the Sema object.
  bool OldCollectStats = PrintStats;
  std::swap(OldCollectStats, S.CollectStats);

  clang::ASTConsumer *Consumer = &S.getASTConsumer();

  clang::Parser *Parser = new clang::Parser(S.getPreprocessor(), S, SkipFunctionBodies);
  clang::Parser &P = *Parser;

  S.getPreprocessor().EnterMainSourceFile();
  P.Initialize();

  // C11 6.9p1 says translation units must have at least one top-level
  // declaration. C++ doesn't have this restriction. We also don't want to
  // complain if we have a precompiled header, although technically if the PCH
  // is empty we should still emit the (pedantic) diagnostic.
  clang::Parser::DeclGroupPtrTy ADecl;
  clang::ExternalASTSource *External = S.getASTContext().getExternalSource();
  if (External)
    External->StartTranslationUnit(Consumer);

  if (P.ParseTopLevelDecl(ADecl)) {
    if (!External && !S.getLangOpts().CPlusPlus)
      P.Diag(clang::diag::ext_empty_translation_unit);
  } else {
    do {
      // If we got a null return and something *was* parsed, ignore it.  This
      // is due to a top-level semicolon, an action override, or a parse error
      // skipping something.
      if (ADecl && !Consumer->HandleTopLevelDecl(ADecl.get()))
        return;
    } while (!P.ParseTopLevelDecl(ADecl));
  }

  // Process any TopLevelDecls generated by #pragma weak.
  for (llvm::SmallVectorImpl<clang::Decl *>::iterator
       I = S.WeakTopLevelDecls().begin(),
       E = S.WeakTopLevelDecls().end(); I != E; ++I)
    Consumer->HandleTopLevelDecl(clang::DeclGroupRef(*I));
  
  Consumer->HandleTranslationUnit(S.getASTContext());

  std::swap(OldCollectStats, S.CollectStats);
  if (PrintStats) {
    llvm::errs() << "\nSTATISTICS:\n";
    P.getActions().PrintStats();
    S.getASTContext().PrintStats();
    clang::Decl::PrintStats();
    clang::Stmt::PrintStats();
    Consumer->PrintStats();
  }
}

static inline void add_directory(clang::Preprocessor &pp, clang::FileManager &fm, clang::SrcMgr::CharacteristicKind flag, const char *dirname)
{
  auto dir = fm.getDirectory(dirname);
  if (dir == NULL)
    JL_PRINTF(JL_STDERR,"WARNING: Could not add directory %s to clang search path!\n",dirname);
  else
    pp.getHeaderSearchInfo().AddSearchPath(clang::DirectoryLookup(dir,flag,false),flag == clang::SrcMgr::C_System || flag == clang::SrcMgr::C_ExternCSystem);

}

DLLEXPORT void init_header(char *name)
{
    clang::FileManager &fm = clang_compiler->getFileManager();
    clang::Preprocessor &pp = clang_compiler->getPreprocessor();
    /*clang::HeaderSearchOptions &opts = pp.getHeaderSearchInfo().getHeaderSearchOpts();
    opts.UseBuiltinIncludes = 0;
    opts.UseStandardSystemIncludes = 0;
    opts.UseStandardCXXIncludes = 0;
    opts.UseLibcxx = 1;
    opts.Verbose = 1;*/
    #define DIR(X) pp.getHeaderSearchInfo().AddSearchPath(clang::DirectoryLookup(fm.getDirectory(X),clang::SrcMgr::C_User,false),false);
    #ifdef OS_LINUX
    add_directory(pp,fm,clang::SrcMgr::C_System,"/usr/include/c++/4.8");
    add_directory(pp,fm,clang::SrcMgr::C_System,"/usr/include/x86_64-linux-gnu/c++/4.8/");
    add_directory(pp,fm,clang::SrcMgr::C_System,"/home/kfischer/julia/usr/lib/clang/3.5/include/");
    add_directory(pp,fm,clang::SrcMgr::C_User,"/home/kfischer/julia/src/support/");
    add_directory(pp,fm,clang::SrcMgr::C_User,"/home/kfischer/julia/usr/include/");
    add_directory(pp,fm,clang::SrcMgr::C_User,"/home/kfischer/julia/deps/llvm-svn/tools/clang/");
    add_directory(pp,fm,clang::SrcMgr::C_User,"/home/kfischer/julia/deps/llvm-svn/tools/clang/include/");
    #else 
    //add_directory(pp,fm,clang::SrcMgr::C_System,"/usr/include");
    add_directory(pp,fm,clang::SrcMgr::C_ExternCSystem,"/Users/kfischer/julia-upstream/usr/lib/clang/3.5.0/include/");
    add_directory(pp,fm,clang::SrcMgr::C_ExternCSystem,"/Users/kfischer/julia/deps/llvm-3.3/projects/libcxx/include/");
    //add_directory(pp,fm,clang::SrcMgr::C_User,"/Users/kfischer/julia-upstream/src/support");
    add_directory(pp,fm,clang::SrcMgr::C_User,"/Users/kfischer/julia-upstream/usr/include");
    add_directory(pp,fm,clang::SrcMgr::C_User,"/Users/kfischer/julia-upstream/deps/llvm-svn/tools/clang/");
    add_directory(pp,fm,clang::SrcMgr::C_User,"/Users/kfischer/julia-upstream/deps/llvm-svn/tools/clang/include/");
    #endif
    clang_compiler->getDiagnosticClient().BeginSourceFile(clang_compiler->getLangOpts(), 0);
    pp.getBuiltinInfo().InitializeBuiltins(pp.getIdentifierTable(),
                                           clang_compiler->getLangOpts());
    pp.enableIncrementalProcessing();
    clang::FrontendInputFile fi = clang::FrontendInputFile(name,clang::IK_CXX);
    clang_compiler->InitializeSourceManager(fi);
    myParseAST(clang_compiler->getSema(),false,false);
    clang_compiler->getSema().PerformPendingInstantiations(false);
}

DLLEXPORT void init_julia_clang_env() {
    //copied from http://www.ibm.com/developerworks/library/os-createcompilerllvm2/index.html
    clang_compiler = new clang::CompilerInstance;
    clang_compiler->createDiagnostics();
    clang_compiler->getLangOpts().CPlusPlus = 1;
    clang_compiler->getLangOpts().CPlusPlus11 = 1;
    clang_compiler->getLangOpts().LineComment = 1;
    clang_compiler->getLangOpts().Bool = 1;
    clang_compiler->getLangOpts().WChar = 1;
    clang_compiler->getLangOpts().C99 = 1;
    clang_compiler->getLangOpts().ImplicitInt = 0;
    clang_compiler->getHeaderSearchOpts().UseBuiltinIncludes = 1;
    clang_compiler->getHeaderSearchOpts().UseLibcxx = 1;
    clang_compiler->getHeaderSearchOpts().UseStandardSystemIncludes = 1;
    clang_compiler->getHeaderSearchOpts().UseStandardCXXIncludes = 1;
    clang_compiler->getCodeGenOpts().setDebugInfo(clang::CodeGenOptions::NoDebugInfo);
    clang_compiler->getTargetOpts().Triple = "x86_64-apple-darwin12.4.0";
    clang::TargetInfo *tin = clang::TargetInfo::CreateTargetInfo(clang_compiler->getDiagnostics(), &clang_compiler->getTargetOpts());
    clang_compiler->setTarget(tin);
    clang_compiler->createFileManager();
    clang_compiler->createSourceManager(clang_compiler->getFileManager());
    clang_compiler->createPreprocessor(clang::TU_Prefix);
    clang_compiler->createASTContext();
    clang_shadow_module = new llvm::Module("clangShadow",jl_LLVMContext);
    clang_astcontext = &clang_compiler->getASTContext();
    clang_compiler->setASTConsumer(new JuliaCodeGenerator());
    clang_compiler->createSema(clang::TU_Prefix,NULL);
    TD = new DataLayout(tin->getTargetDescription());
    clang_cgm = new clang::CodeGen::CodeGenModule(
        *clang_astcontext,
        clang_compiler->getCodeGenOpts(),
        *clang_shadow_module,
        *TD,
        clang_compiler->getDiagnostics());
    clang_cgt = &(clang_cgm->getTypes());
    clang_cgf = new clang::CodeGen::CodeGenFunction(*clang_cgm);
    clang_cgf->CurFuncDecl = NULL;
    clang_cgf->CurCodeDecl = NULL;

    cT_int1  = clang_astcontext->BoolTy.getTypePtrOrNull();
    cT_int8  = clang_astcontext->SignedCharTy.getTypePtrOrNull();
    cT_uint8 = clang_astcontext->UnsignedCharTy.getTypePtrOrNull();
    cT_int16 = clang_astcontext->ShortTy.getTypePtrOrNull();
    cT_uint16 = clang_astcontext->UnsignedShortTy.getTypePtrOrNull();
    cT_int32 = clang_astcontext->IntTy.getTypePtrOrNull();
    cT_uint32 = clang_astcontext->UnsignedIntTy.getTypePtrOrNull();
    cT_char = clang_astcontext->IntTy.getTypePtrOrNull();
#ifdef __LP64__
    cT_int64 = clang_astcontext->LongTy.getTypePtrOrNull();
    cT_uint64 = clang_astcontext->UnsignedLongTy.getTypePtrOrNull();
#else
    cT_int64 = clang_astcontext->LongLongTy.getTypePtrOrNull();
    cT_uint64 = clang_astcontext->UnsignedLongLongTy.getTypePtrOrNull();
#endif
    cT_size = clang_astcontext->getSizeType().getTypePtrOrNull();
    cT_int128 = clang_astcontext->Int128Ty.getTypePtrOrNull();
    cT_uint128 = clang_astcontext->UnsignedInt128Ty.getTypePtrOrNull();
    cT_complex64 = clang_astcontext->FloatComplexTy.getTypePtrOrNull();
    cT_complex128 = clang_astcontext->DoubleComplexTy.getTypePtrOrNull();

    cT_float32 = clang_astcontext->FloatTy.getTypePtrOrNull();
    cT_float64 = clang_astcontext->DoubleTy.getTypePtrOrNull();
    cT_void = clang_astcontext->VoidTy.getTypePtrOrNull();

    cT_pvoid = clang_astcontext->getPointerType(clang_astcontext->VoidTy).getTypePtrOrNull();
}

static llvm::Module *cur_module = NULL;
static llvm::Function *cur_func = NULL;


DLLEXPORT void *setup_cpp_env(void *module, void *jlfunc)
{
    //assert(in_cpp == false);
    //in_cpp = true;

    cppcall_state_t *state = new cppcall_state_t;
    state->module = cur_module;
    state->func = cur_func;
    state->CurFn = clang_cgf->CurFn;
    state->block = clang_cgf->Builder.GetInsertBlock();
    state->point = clang_cgf->Builder.GetInsertPoint();
    state->prev_alloca_bb_ptr = clang_cgf->AllocaInsertPt;

    llvm::Function *w = (Function *)jlfunc;
    assert(w != NULL);
    assert(clang_cgf != NULL);
    cur_module = (llvm::Module*)module;
    cur_func = w;

    Function *ShadowF = Function::Create(w->getFunctionType(),
        Function::ExternalLinkage,
        w->getName(),
        clang_shadow_module);    

    BasicBlock *b0 = BasicBlock::Create(cur_module->getContext(), "top", ShadowF);

    // setup the environment to clang's expecations
    clang_cgf->Builder.SetInsertPoint( b0 );
    // clang expects to alloca memory before the AllocaInsertPt
    // typically, clang would create this pointer when it started emitting the function
    // instead, we create a dummy reference here
    // for efficiency, we avoid creating a new placehold instruction if possible
    llvm::Instruction *alloca_bb_ptr = NULL;
    if (b0->empty()) {
        llvm::Value *Undef = llvm::UndefValue::get(T_int32);
        clang_cgf->AllocaInsertPt = alloca_bb_ptr = new llvm::BitCastInst(Undef, T_int32, "", b0);
    } else {
        clang_cgf->AllocaInsertPt = &(b0->front());
    }

    clang_cgf->CurFn = ShadowF;
    state->alloca_bb_ptr = alloca_bb_ptr;

    return state;
}

/*
class FunctionMover;

static Function *myCloneFunction(llvm::Function *toClone,FunctionMover *mover);

class FunctionMover : public ValueMaterializer
{
public:
    FunctionMover(llvm::Module *dest,llvm::Module *src) :
        ValueMaterializer(), destModule(dest), srcModule(src), VMap()
    {

    } 
    ValueToValueMapTy VMap;
    llvm::Module *destModule;
    llvm::Module *srcModule;
    virtual Value *materializeValueFor (Value *V)
    {
        Function *F = dyn_cast<Function>(V);
        if(F)
        {
            if(F->isIntrinsic())
                return destModule->getOrInsertFunction(F->getName(),F->getFunctionType());
            if(F->isDeclaration() || F->getParent() != destModule)
            {
                Function *shadow = srcModule->getFunction(F->getName());
                if (shadow != NULL && !shadow->isDeclaration())
                {
                    // Not truly external
                    // Check whether we already emitted it once
                    uint64_t addr = jl_mcjmm->getSymbolAddress(F->getName());
                    if(addr == 0)
                    {
                        return myCloneFunction(shadow,this);
                    } else {
                        return destModule->getOrInsertFunction(F->getName(),F->getFunctionType());
                    }
                } else if (!F->isDeclaration())
                {
                    return myCloneFunction(F,this);
                }
            }
            // Still a declaration and still in a diffrent module
            if(F->isDeclaration() && F->getParent() != destModule)
            {
                // Create forward declaration in current module
                return destModule->getOrInsertFunction(F->getName(),F->getFunctionType());
            }
        } else if (isa<GlobalVariable>(V))
        {
            GlobalVariable *GV = cast<GlobalVariable>(V);
            assert(GV != NULL);
            GlobalVariable *newGV = new GlobalVariable(*destModule,
                GV->getType()->getElementType(),
                GV->isConstant(),
                GlobalVariable::ExternalLinkage,
                NULL,
                GV->getName());
            newGV->copyAttributesFrom(GV);
            if (GV->isDeclaration())
                return newGV;
            uint64_t addr = jl_mcjmm->getSymbolAddress(GV->getName());
            if(addr != 0)
            {
                newGV->setExternallyInitialized(true);
                return newGV;
            }
            if(GV->getInitializer() != NULL) {
                Value *C = MapValue(GV->getInitializer(),VMap,RF_None,NULL,this);
                newGV->setInitializer(cast<Constant>(C));
            }
            return newGV;
        }
        return NULL;
    };
};

static Function *myCloneFunction(llvm::Function *toClone,FunctionMover *mover)
{
    Function *NewF = Function::Create(toClone->getFunctionType(),
        Function::ExternalLinkage,
        toClone->getName(),
        mover->destModule);    
    ClonedCodeInfo info;
    Function::arg_iterator DestI = NewF->arg_begin();
    for (Function::const_arg_iterator I = toClone->arg_begin(), E = toClone->arg_end();
      I != E; ++I) {
        //if (mover->VMap.count(I) == 0) {   // Is this argument preserved?
            DestI->setName(I->getName()); // Copy the name over...
            mover->VMap[I] = DestI++;        // Add mapping to VMap
        //}
    }

    // Necessary in case the function is self referential
    mover->VMap[toClone] = NewF;

    SmallVector<ReturnInst*, 8> Returns;
    llvm::CloneFunctionInto(NewF,toClone,mover->VMap,true,Returns,"",NULL,NULL,mover);

    return NewF;
}*/


DLLEXPORT void copy_into(llvm::Function *src, llvm::Function *dest)
{
    FunctionMover mover(dest->getParent(),src->getParent());
    Function::arg_iterator DestI = dest->arg_begin();
    for (Function::const_arg_iterator I = src->arg_begin(), E = src->arg_end();
      I != E; ++I) {
        //if (mover->VMap.count(I) == 0) {   // Is this argument preserved?
            mover.VMap[DestI] = DestI;
            mover.VMap[I] = DestI++;        // Add mapping to VMap
        //}
    }  

    dest->deleteBody();

    SmallVector<ReturnInst*, 8> Returns;
    llvm::CloneFunctionInto(dest,src,mover.VMap,true,Returns,"",NULL,NULL,&mover);
}

DLLEXPORT void cleanup_cpp_env(cppcall_state_t *state)
{
    //assert(in_cpp == true);
    //in_cpp = false;

    clang_compiler->getSema().PerformPendingInstantiations(false);
    clang_cgm->Release();

    // Set all functions and globals to external linkage (MCJIT needs this ugh)
    for(Module::global_iterator I = jl_Module->global_begin(),
            E = jl_Module->global_end(); I != E; ++I) {
        I->setLinkage(llvm::GlobalVariable::ExternalLinkage);
    }

    Function *F = clang_cgf->CurFn;

    // cleanup the environment
    clang_cgf->AllocaInsertPt = 0; // free this ptr reference
    if (state->alloca_bb_ptr)
        state->alloca_bb_ptr->eraseFromParent(); 

    copy_into(F,cur_func);

    F->eraseFromParent();

    cur_module = state->module;
    cur_func = state->func;
    clang_cgf->CurFn = state->CurFn;
    clang_cgf->Builder.SetInsertPoint(state->block,state->point);
    clang_cgf->AllocaInsertPt = state->prev_alloca_bb_ptr;
    delete state;
}

DLLEXPORT void emit_cpp_new(void *type)
{
    clang::Decl* MD = ((clang::Decl *)type);
    clang::CXXRecordDecl* cdecl = dyn_cast<clang::CXXRecordDecl>(MD);
    clang::FunctionDecl *OperatorNew = NULL;
    clang::FunctionDecl *OperatorDelete = NULL;

    clang::ASTContext &astctx = MD->getASTContext();
    clang_compiler->setASTContext(&astctx);

    bool globalNew = false;
    clang::QualType ty = clang::QualType(cdecl->getTypeForDecl(),0);

    clang::Sema &sema = clang_compiler->getSema();

    // TODO: This may be incorrect.
    sema.CurContext = MD->getDeclContext();

#ifdef LLVM34
    sema.FindAllocationFunctions(clang::SourceLocation(),clang::SourceLocation(),globalNew,
    ty,false,clang::MultiExprArg(),OperatorNew,OperatorDelete);
#else
    sema.FindAllocationFunctions(clang::SourceLocation(),clang::SourceLocation(),globalNew,
    ty,false,0,NULL,OperatorNew,OperatorDelete);
#endif

    Value *ret = clang_cgf->EmitCXXNewExpr(new (astctx) clang::CXXNewExpr(MD->getASTContext(),globalNew,OperatorNew,OperatorDelete,false,ArrayRef< clang::Expr * >(),
        clang::SourceRange(),
        NULL,                       //Array Size
        clang::CXXNewExpr::NoInit,  //Initialization Style
        clang::CXXConstructExpr::Create(
            astctx,
            ty,
            clang::SourceLocation(),
            sema.LookupDefaultConstructor(cdecl),
            false,
            ArrayRef< clang::Expr * >(),
            false,
            false,
            false,
            clang::CXXConstructExpr::CK_Complete,
            clang::SourceRange()
        ),                       //Initializer
        astctx.getPointerType(ty),  //Allocated Type
        NULL,                       //Type Source Info
        clang::SourceRange(),
        clang::SourceRange()
        ));

    clang_cgf->Builder.CreateRet(clang_cgf->Builder.CreateBitCast(ret,clang_cgf->CurFn->getReturnType()));
}

/*
DLLEXPORT extern "C" void *construct_CXXTemporaryObjectExpr(void *d)
{
    clang::Decl* MD = ((clang::Decl *)type);
    clang::CXXRecordDecl* cdecl = dyn_cast<clang::CXXRecordDecl>(MD);
    // Find Constructor
    clang::CXXConstructorDecl *ctor = NULL;
    for (clang::CXXRecordDecl::ctor_iterator it = cdecl->ctor_begin(); it != cdecl->ctor_end(); it++))
    {
        if ((*it)->getMinRequiredArguments() == 0) {
            ctor = *it;
            break;
        }
    }
    return new (clang_astctx) clang::CXXTemporaryObjectExpr(clang_astctx,ctor,NULL,ArrayRef<Expr*>(),SourceRange(),false,false,false);
}
 */

DLLEXPORT int RequireCompleteType(clang::Type *t)
{
  clang::Sema &sema = clang_compiler->getSema();
  return sema.RequireCompleteType(clang::SourceLocation(),clang::QualType(t,0),0);
}

DLLEXPORT void *typeconstruct(clang::Type *t, clang::Expr **rawexprs, size_t nexprs)
{
    clang::QualType Ty(t,0);
    clang::MultiExprArg Exprs(rawexprs,nexprs);

    clang::Sema &sema = clang_compiler->getSema();
    clang::TypeSourceInfo *TInfo = clang_astcontext->getTrivialTypeSourceInfo(Ty);

    if (Ty->isDependentType() || clang::CallExpr::hasAnyTypeDependentArguments(Exprs)) {
        return clang::CXXUnresolvedConstructExpr::Create(*clang_astcontext, TInfo,
                                                      clang::SourceLocation(),
                                                      Exprs,
                                                      clang::SourceLocation());
    }
  
    clang::ExprResult Result;

    if (Exprs.size() == 1) {
        clang::Expr *Arg = Exprs[0];
        Result = sema.BuildCXXFunctionalCastExpr(TInfo, clang::SourceLocation(), Arg, clang::SourceLocation());
        assert(!Result.isInvalid());
        return Result.get();
    }

    if (!Ty->isVoidType() &&
        sema.RequireCompleteType(clang::SourceLocation(), Ty,
                            clang::diag::err_invalid_incomplete_type_use)) {
        assert(false);
        return NULL;
    }

    if (sema.RequireNonAbstractType(clang::SourceLocation(), Ty,
                               clang::diag::err_allocation_of_abstract_type)) {
        assert(false);
        return NULL;
    }

    clang::InitializedEntity Entity = clang::InitializedEntity::InitializeTemporary(TInfo);
    clang::InitializationKind Kind =
        Exprs.size() ?  clang::InitializationKind::CreateDirect(clang::SourceLocation(), clang::SourceLocation(), clang::SourceLocation())
        : clang::InitializationKind::CreateValue(clang::SourceLocation(), clang::SourceLocation(), clang::SourceLocation());
    clang::InitializationSequence InitSeq(sema, Entity, Kind, Exprs);
    Result = InitSeq.Perform(sema, Entity, Kind, Exprs);

    assert(!Result.isInvalid());
    return Result.get();
}

DLLEXPORT void *build_call_to_member(clang::Expr *MemExprE,clang::Expr **exprs, size_t nexprs)
{
    return (void*)clang_compiler->getSema().BuildCallToMemberFunction(NULL,MemExprE,clang::SourceLocation(),clang::MultiExprArg(exprs,nexprs),clang::SourceLocation()).get();
}

DLLEXPORT void *CreateParmVarDecl(clang::Type *type)
{
    clang::QualType T(type,0);
    clang::ParmVarDecl *d = clang::ParmVarDecl::Create(   
        *clang_astcontext,
        clang_astcontext->getTranslationUnitDecl(), // This is wrong, hopefully it doesn't matter
        clang::SourceLocation(),
        clang::SourceLocation(),
        &clang_compiler->getPreprocessor().getIdentifierTable().getOwn("dummy"),
        T,
        clang_astcontext->getTrivialTypeSourceInfo(T),
        clang::SC_None,NULL);

    return (void*)(clang::Decl*)d;
}

DLLEXPORT void AssociateValue(clang::Decl *d, clang::Type *type, llvm::Value *V)
{
    clang::VarDecl *vd = dyn_cast<clang::VarDecl>(d);
    clang::QualType T(type,0);
    llvm::Type *Ty = clang_cgf->ConvertTypeForMem(T);
    // Associate the value with this decl
    clang_cgf->EmitParmDecl(*vd, clang_cgf->Builder.CreateBitCast(V, Ty), false, 0);
}

DLLEXPORT void *CreateDeclRefExpr(clang::ValueDecl *D, clang::Type *type)
{
    clang::QualType T(type,0);
    return (void*)clang::DeclRefExpr::Create(*clang_astcontext, clang::NestedNameSpecifierLoc(NULL,NULL), clang::SourceLocation(), 
            D, false, clang::SourceLocation(), T.getNonReferenceType(), clang::VK_LValue);
}

DLLEXPORT void *CreateMemberExpr(clang::Expr *base, int isarrow, clang::ValueDecl *memberdecl)
{
    return (void*)(clang::Expr*)clang::MemberExpr::Create (
        *clang_astcontext, 
        base,
        isarrow, 
        clang::NestedNameSpecifierLoc(), 
        clang::SourceLocation(),
        memberdecl, 
        clang::DeclAccessPair::make(memberdecl,clang::AS_public), 
        clang::DeclarationNameInfo (memberdecl->getDeclName(),clang::SourceLocation()), 
        NULL, clang_astcontext->BoundMemberTy, clang::VK_RValue, clang::OK_Ordinary);
}

DLLEXPORT void *tovdecl(clang::Decl *D)
{
    return dyn_cast<clang::ValueDecl>(D);
}

DLLEXPORT void *cxxtmplt(clang::Decl *D)
{
  return dyn_cast<clang::ClassTemplateDecl>(D);
}

DLLEXPORT void *SpecializeClass(clang::ClassTemplateDecl *tmplt, clang::Type **types, size_t nargs)
{
  clang::TemplateArgument *targs = new clang::TemplateArgument[nargs];
  for (size_t i = 0; i < nargs; ++i)
    targs[i] = clang::TemplateArgument(clang::QualType(types[i],0));
  void *InsertPos;
  auto ret = tmplt->findSpecialization(targs,nargs,InsertPos);
  delete[] targs;
  return ret;
}

DLLEXPORT void *emitcppmembercallexpr(clang::CXXMemberCallExpr *E, llvm::Value *rslot)
{
    clang::CodeGen::RValue ret = clang_cgf->EmitCXXMemberCallExpr(E,clang::CodeGen::ReturnValueSlot(rslot,false));
    if (ret.isScalar())
      return ret.getScalarVal();
    else
      return ret.getAggregateAddr();
}

DLLEXPORT void emitexprtomem(clang::Expr *E, llvm::Value *addr, int isInit)
{
    clang_cgf->EmitAnyExprToMem(E, addr, clang::Qualifiers(), isInit);
}

/*
Sema::BuildCallToMemberFunction(Scope *S, Expr *MemExprE,
                                SourceLocation LParenLoc,
                                MultiExprArg Args,
                                SourceLocation RParenLoc) {
                                    */

DLLEXPORT void *get_nth_argument(Function *f, size_t n)
{
    size_t i = 0;
    Function::arg_iterator AI = f->arg_begin();
    for (; AI != f->arg_end(); ++i, ++AI)
    {  
        if (i == n)
            return (void*)((Value*)AI++);
    }
    return NULL;
}

DLLEXPORT void *create_extract_value(Value *agg, size_t idx)
{
    return clang_cgf->Builder.CreateExtractValue(agg,ArrayRef<unsigned>((unsigned)idx));
}

DLLEXPORT void *create_insert_value(Value *agg, Value *val, size_t idx)
{
    return clang_cgf->Builder.CreateInsertValue(agg,val,ArrayRef<unsigned>((unsigned)idx));
}

DLLEXPORT void *lookup_name(char *name, clang::Decl *decl)
{
    clang::SourceManager &sm = clang_compiler->getSourceManager();
    clang::CXXScopeSpec spec;
    spec.setBeginLoc(sm.getLocForStartOfFile(sm.getMainFileID()));
    spec.setEndLoc(sm.getLocForStartOfFile(sm.getMainFileID()));
    clang::DeclarationName DName(&clang_astcontext->Idents.get(name));
    clang::Sema &cs = clang_compiler->getSema();
    clang::DeclContext *ctx = dyn_cast<clang::DeclContext>(decl);
    cs.RequireCompleteDeclContext(spec,ctx);
    //return ctx->lookup(DName).front();
    clang::LookupResult R(cs, DName, clang::SourceLocation(), clang::Sema::LookupAnyName);
    cs.LookupQualifiedName(R, ctx, false);
    return R.empty() ? NULL : R.getRepresentativeDecl();
}

DLLEXPORT void *tu_decl()
{
    return clang_astcontext->getTranslationUnitDecl();
}

DLLEXPORT void *get_primary_dc(clang::DeclContext *dc)
{
    return dc->getPrimaryContext();
}

DLLEXPORT void *decl_context(clang::Decl *decl)
{
    if(isa<clang::TypedefNameDecl>(decl))
    {
        decl = dyn_cast<clang::TypedefNameDecl>(decl)->getUnderlyingType().getTypePtr()->getAsCXXRecordDecl(); 
    }
    /*
    if(isa<clang::ClassTemplateSpecializationDecl>(decl))
    {
        auto ptr = cast<clang::ClassTemplateSpecializationDecl>(decl)->getSpecializedTemplateOrPartial();
        if (ptr.is<clang::ClassTemplateDecl*>())
            decl = ptr.get<clang::ClassTemplateDecl*>();
        else
            decl = ptr.get<clang::ClassTemplatePartialSpecializationDecl*>();
    }*/
    return dyn_cast<clang::DeclContext>(decl);
}

DLLEXPORT void *to_decl(clang::DeclContext *decl)
{
    return dyn_cast<clang::Decl>(decl);
}

DLLEXPORT void *to_cxxdecl(clang::Decl *decl)
{
    return dyn_cast<clang::CXXRecordDecl>(decl);
}

DLLEXPORT void *get_result_type(void *cppfunc)
{
    clang::Decl* MD = ((clang::Decl *)cppfunc);
    clang::FunctionDecl* fdecl = dyn_cast<clang::FunctionDecl>(MD);
    if (fdecl == NULL)
        return NULL;
    return (void*)fdecl->getReturnType().getTypePtr();
}

DLLEXPORT void *emit_field_ref(clang::Type *BaseType, Value *BaseVal, clang::FieldDecl *FieldDecl)
{
    clang::CodeGen::LValue BaseLV = clang_cgf->MakeNaturalAlignAddrLValue(BaseVal,clang::QualType(BaseType,0));
    clang::CodeGen::LValue LV = clang_cgf->EmitLValueForField(BaseLV,FieldDecl);
    return LV.getAddress();
}

DLLEXPORT Value *emit_cpp_call(void *cppfunc, Value **args, clang::Type **types, clang::Expr **xexprs, size_t nargs, bool Forward, bool EmitReturn)
{
    clang::Decl* MD = ((clang::Decl *)cppfunc);
    clang::FunctionDecl* fdecl = dyn_cast<clang::FunctionDecl>(MD);

    clang::VarDecl *decls[nargs];
    clang::Expr *exprs[nargs];

    clang::CXXMethodDecl *cxx = dyn_cast<clang::CXXMethodDecl>(fdecl);
    bool isMemberCall = cxx != NULL && !cxx->isStatic();
    size_t nparams = isMemberCall ? nargs-1 : nargs;

    clang::FunctionDecl::param_const_iterator it = fdecl->param_begin();
    if (xexprs == NULL) {
        for ( int i = 0, j = 0; i < nparams; ++i )
        {
            clang::QualType T;
            if (types[i] == NULL) {
                while (j != i) {
                    ++j;
                    ++it;
                }
                T = (*it)->getOriginalType();
            } else {
                T = clang::QualType(types[i+isMemberCall],(unsigned)0);
            }

            
            decls[i] = clang::ParmVarDecl::Create(   
                *clang_astcontext,
                fdecl, // This is wrong, hopefully it doesn't matter
                clang::SourceLocation(),
                clang::SourceLocation(),
                &clang_compiler->getPreprocessor().getIdentifierTable().getOwn("dummy"),
                T,
                clang_astcontext->getTrivialTypeSourceInfo(T),
                clang::SC_None,NULL);

            // Associate the value with this decl
            clang_cgf->EmitParmDecl(*decls[i], clang_cgf->Builder.CreateBitCast(args[i+isMemberCall], 
                clang_cgf->ConvertTypeForMem(T)), false, 0);

            exprs[i] = clang::DeclRefExpr::Create(*clang_astcontext, clang::NestedNameSpecifierLoc(NULL,NULL), clang::SourceLocation(), 
                decls[i], false, clang::SourceLocation(), T.getNonReferenceType(), clang::VK_LValue);
        }
    } else {
      for ( int i = 0, j = 0; i < nparams; ++i )
        exprs[i] = xexprs[i];
    }

    const clang::CodeGen::CGFunctionInfo &cgfi = clang_cgt->arrangeFunctionDeclaration(fdecl);
    const clang::FunctionType *FT = fdecl->getType()->getAs<clang::FunctionType>();

    const clang::FunctionProtoType *FPT = dyn_cast<clang::FunctionProtoType>(FT);
    assert(FPT);

    clang::Sema &sema = clang_compiler->getSema();

    SmallVector<clang::Expr *, 8> AllArgs;
    if (nparams > 0) {
        bool error = sema.GatherArgumentsForCall(clang::SourceLocation(),fdecl,FPT,0,
            llvm::ArrayRef<clang::Expr*>((clang::Expr**)&exprs,nparams),
            AllArgs,clang::Sema::VariadicDoesNotApply,false,false);
        assert(!error);
    }

    clang::ASTContext &astctx = MD->getASTContext();

    clang::DeclRefExpr *DRE =
    new (astctx) clang::DeclRefExpr(fdecl, false, fdecl->getType(), clang::VK_LValue, clang::SourceLocation());

    clang::ImplicitCastExpr *ICE = 
    clang::ImplicitCastExpr::Create(astctx, astctx.getPointerType(fdecl->getType()), clang::CK_FunctionToPointerDecay,
                             DRE, 0, clang::VK_RValue);


    // emit the actual call
    clang::CodeGen::ReturnValueSlot return_slot;
    clang::CodeGen::CallArgList argvals;
    it = fdecl->param_begin();
    if(Forward)
    {
        Function::arg_iterator AI = clang_cgf->CurFn->arg_begin();
        if(isMemberCall)
        {
            clang::CXXMethodDecl *cxx = dyn_cast<clang::CXXMethodDecl>(fdecl);
            if(!cxx->isStatic())
                argvals.add(clang::CodeGen::RValue::get(AI++),cxx->getThisType(astctx));
        }
        if(AI != clang_cgf->CurFn->arg_end()) {
            for (; it != fdecl->param_end(); ++it)
            {
                argvals.add(clang::CodeGen::RValue::get(AI++),(*it)->getOriginalType());
                if(AI == clang_cgf->CurFn->arg_end()) {
                    ++it;
                    break;
                }
            }
        }
    }
    else
    {
        size_t i = 0;
        if(isMemberCall)
        {
            clang::CXXMethodDecl *cxx = dyn_cast<clang::CXXMethodDecl>(fdecl);
            if(!cxx->isStatic())
                argvals.add(clang::CodeGen::RValue::get(args[0]),cxx->getThisType(astctx));
        }
        for (; i < nparams; ++i, ++it) {
            clang::Expr *E = AllArgs[i];
            clang::QualType T = types[i]==NULL?(*it)->getOriginalType():clang::QualType(types[i],0);
            if (E->isGLValue()) {
                assert(E->getObjectKind() == clang::OK_Ordinary);
                argvals.add(clang_cgf->EmitReferenceBindingToExpr(E), T);
            } else {
                argvals.add(clang_cgf->EmitAnyExprToTemp(E),T);
            }
        }
    }

    // emit default arguments
    for(; it != fdecl->param_end(); ++it)
    {
        assert((*it)->hasDefaultArg());
        clang::QualType T = (*it)->getOriginalType();
        clang::Expr *E = sema.BuildCXXDefaultArgExpr(clang::SourceLocation(),fdecl,*it).get();
        if (T->isReferenceType())
        {
#ifdef LLVM34
            argvals.add(clang_cgf->EmitReferenceBindingToExpr(E),T);
#else
            argvals.add(clang_cgf->EmitReferenceBindingToExpr(E,NULL),T);
#endif
        } else {
            argvals.add(clang_cgf->EmitAnyExpr(E),T);
        }
    }

    llvm::FunctionType *Ty = clang_cgm->getTypes().GetFunctionType(cgfi);
    clang::CodeGen::RValue rv;
    sema.MarkFunctionReferenced(clang::SourceLocation(),fdecl);
    if(isa<clang::CXXMethodDecl>(fdecl))
    {
        clang::CXXMethodDecl *cxx = dyn_cast<clang::CXXMethodDecl>(fdecl);

        // Well, let's try this, shall we?
        //if (cxx->doesThisDeclarationHaveABody())
        //    clang_cgm->EmitTopLevelDecl(cxx);

        rv = clang_cgf->EmitCall(
            cgfi, clang_cgm->GetAddrOfFunction(cxx,Ty), return_slot,
            argvals, NULL, NULL);

    } else {
        rv = clang_cgf->EmitCall(
            cgfi, clang_cgf->EmitScalarExpr(ICE), return_slot,
            argvals, NULL, NULL);
    }

    assert(rv.isScalar());
    Value *ret = rv.getScalarVal();

    if(EmitReturn) {
        // Funnily the RetVoid won't actually be inserted into the basic block
        // of the function if ret == NULL. Instead clan
        if (ret == NULL || ret->getType() == T_void)
            clang_cgf->Builder.CreateRetVoid();
        else
            clang_cgf->Builder.CreateRet(clang_cgf->Builder.CreateBitCast(ret,clang_cgf->CurFn->getReturnType()));
    }

    return ret;
}

DLLEXPORT char *decl_name(clang::NamedDecl *decl)
{
    std::string str = decl->getQualifiedNameAsString().data();
    char * cstr = (char*)malloc(str.length()+1);
    std::strcpy (cstr, str.c_str());
    return cstr;
}

DLLEXPORT void *referenced_type(clang::Type *t)
{
    return (void*)t->getPointeeType().getTypePtr();
}
DLLEXPORT void *getPointerTo(clang::Type *t)
{
    return (void*)clang_astcontext->getPointerType(clang::QualType(t,0)).getTypePtr();
}

DLLEXPORT void *getReferenceTo(clang::Type *t)
{
    return (void*)clang_astcontext->getLValueReferenceType(clang::QualType(t,0)).getTypePtr();
}

DLLEXPORT void *createDeref(clang::Type *type, llvm::Value *value)
{
    clang::QualType T(type,0);

    clang::VarDecl *decl = clang::ParmVarDecl::Create(   
    *clang_astcontext,
    clang_astcontext->getTranslationUnitDecl(), // This is wrong, hopefully it doesn't matter
    clang::SourceLocation(),
    clang::SourceLocation(),
    &clang_compiler->getPreprocessor().getIdentifierTable().getOwn("dummy"),
    T,
    clang_astcontext->getTrivialTypeSourceInfo(T),
    clang::SC_None,NULL);

    // Associate the value with this decl
    clang_cgf->EmitParmDecl(*decl, clang_cgf->Builder.CreateBitCast(value, 
        clang_cgf->ConvertTypeForMem(T)), false, 0);

    clang::Expr *expr = clang::DeclRefExpr::Create(*clang_astcontext, clang::NestedNameSpecifierLoc(NULL,NULL), clang::SourceLocation(), 
        decl, false, clang::SourceLocation(), T, clang::VK_RValue);

    return clang_compiler->getSema().CreateBuiltinUnaryOp(clang::SourceLocation(),clang::UO_Deref,expr).get();
}

DLLEXPORT void *createDerefExpr(clang::Expr *expr)
{
  return (void*)clang_compiler->getSema().CreateBuiltinUnaryOp(clang::SourceLocation(),clang::UO_Deref,expr).get();
}

DLLEXPORT void *clang_get_instance()
{
    return clang_compiler;
}

DLLEXPORT void *clang_get_cgm()
{
    return clang_cgm;
}

DLLEXPORT void *clang_get_cgf()
{
    return clang_cgf;
}

DLLEXPORT void *clang_get_cgt()
{
    return clang_cgt;
}

DLLEXPORT void *clang_get_builder()
{
    return (void*)&clang_cgf->Builder;
}

DLLEXPORT void *jl_get_llvm_ee()
{
    return jl_ExecutionEngine;
}

DLLEXPORT void *jl_get_llvmc()
{
    return &jl_LLVMContext;
}

DLLEXPORT void cdump(void *decl)
{
    ((clang::Decl*) decl)->dump();
}

DLLEXPORT void *tollvmty(clang::Type *p)
{
    clang::QualType T(p,0);
    return (void*)clang_cgf->ConvertTypeForMem(T);
}

DLLEXPORT void *createLoad(llvm::IRBuilder<false> *builder, llvm::Value *val)
{
    return builder->CreateLoad(val);
}

DLLEXPORT void *CreateConstGEP1_32(llvm::IRBuilder<false> *builder, llvm::Value *val, uint32_t idx)
{
    return (void*)builder->CreateConstGEP1_32(val,idx);
}

/*
DeduceTemplateArguments (FunctionTemplateDecl *FunctionTemplate, TemplateArgumentListInfo *ExplicitTemplateArgs, ArrayRef< Expr * > Args, FunctionDecl *&Specialization, sema::TemplateDeductionInfo &Info)
*/

DLLEXPORT void *DeduceTemplateArguments(clang::FunctionTemplateDecl *tmplt, clang::Expr **args, uint32_t nargs)
{
    clang::TemplateArgumentListInfo tali;
    clang::sema::TemplateDeductionInfo tdi((clang::SourceLocation()));
    clang::FunctionDecl *decl = NULL;
    clang_compiler->getSema().DeduceTemplateArguments(tmplt, &tali, ArrayRef<clang::Expr *>(args,nargs), decl, tdi);
    return (void*) decl;
}

}
