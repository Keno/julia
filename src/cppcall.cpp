// clang state
#undef B0 //rom termios
#include "llvm/ADT/DenseMapInfo.h"
#include "clang/Sema/ScopeInfo.h"
#include "clang/AST/ASTContext.h"
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
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSwitch.h"
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Frontend/CodeGenOptions.h>
#include <clang/AST/Type.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclTemplate.h>
#include <clang/Basic/Specifiers.h>
#include <CodeGen/CodeGenModule.h>
#include <CodeGen/CodeGenTypes.h>
#include <CodeGen/CodeGenFunction.h>

static clang::ASTContext *clang_astcontext;
static clang::CompilerInstance *clang_compiler;
static clang::CodeGen::CodeGenModule *clang_cgm;
static clang::CodeGen::CodeGenTypes *clang_cgt;
static clang::CodeGen::CodeGenFunction *clang_cgf;

// clang types
static clang::CanQualType cT_int1;
static clang::CanQualType cT_int8;
static clang::CanQualType cT_uint8;
static clang::CanQualType cT_int16;
static clang::CanQualType cT_uint16;
static clang::CanQualType cT_int32;
static clang::CanQualType cT_uint32;
static clang::CanQualType cT_int64;
static clang::CanQualType cT_uint64;
static clang::CanQualType cT_char;
static clang::CanQualType cT_size;
static clang::CanQualType cT_int128;
static clang::CanQualType cT_uint128;
static clang::CanQualType cT_complex64;
static clang::CanQualType cT_complex128;
static clang::CanQualType cT_float32;
static clang::CanQualType cT_float64;
static clang::CanQualType cT_void;
static clang::CanQualType cT_pvoid;

static bool isInitialized = false;

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

class JuliaCodeGenAction : public clang::ASTFrontendAction {
public:
  virtual clang::ASTConsumer *CreateASTConsumer(clang::CompilerInstance &CI,
                                         StringRef InFile) {
    printf("test");
    return new JuliaCodeGenerator();
  }

public:
  JuliaCodeGenAction() {}

  virtual bool hasCodeCompletionSupport() const { return false; }
  virtual clang::TranslationUnitKind getTranslationUnitKind()  { return clang::TU_Prefix; }
};

DLLEXPORT extern "C" void init_header(char *name)
{
    clang::FileManager &fm = clang_compiler->getFileManager();
    clang::Preprocessor &pp = clang_compiler->getPreprocessor();
    //pp.getHeaderSearchInfo().AddSearchPath(clang::DirectoryLookup(fm.getDirectory("/usr/include"),clang::SrcMgr::C_System,false),true);
    //#define DIR(X) pp.getHeaderSearchInfo().AddSearchPath(clang::DirectoryLookup(fm.getDirectory(X),clang::SrcMgr::C_User,false),false);
    //DIR("/Users/kfischer/julia/src/support")
    //DIR("/Users/kfischer/julia/usr/include")
    //DIR("/Users/kfischer/julia/deps/llvm-3.3/tools/clang/include/")
    clang::FrontendInputFile fi = clang::FrontendInputFile(name,clang::IK_CXX);
    JuliaCodeGenAction *a = new JuliaCodeGenAction;
    clang_compiler->getFrontendOpts().Inputs.push_back(fi);
    //clang_compiler->InitializeSourceManager(fi);
    clang_compiler->ExecuteAction(*a);
}


DLLEXPORT extern "C" void init_julia_clang_env(void *module) {
    //copied from http://www.ibm.com/developerworks/library/os-createcompilerllvm2/index.html
    clang_compiler = new clang::CompilerInstance;
    clang_compiler->createDiagnostics();
    clang_compiler->getLangOpts().CPlusPlus = 1;
    clang_compiler->getTargetOpts().Triple = "x86_64-apple-darwin12.4.0";
    clang::TargetInfo *tin = clang::TargetInfo::CreateTargetInfo(clang_compiler->getDiagnostics(), &clang_compiler->getTargetOpts());
    clang_compiler->setTarget(tin);
    clang_compiler->createFileManager();
    clang_compiler->createSourceManager(clang_compiler->getFileManager());
    clang_compiler->createPreprocessor();
    clang_compiler->createASTContext();
    clang_astcontext = &clang_compiler->getASTContext();
    clang_compiler->setASTConsumer(new JuliaCodeGenerator());
    clang_compiler->createSema(clang::TU_Prefix,NULL);
    DataLayout *TD = new DataLayout(tin->getTargetDescription());
    clang_cgm = new clang::CodeGen::CodeGenModule(
            *clang_astcontext,
            clang_compiler->getCodeGenOpts(),
            *((llvm::Module*)module),
            *TD,
            clang_compiler->getDiagnostics());
    clang_cgt = new clang::CodeGen::CodeGenTypes(*clang_cgm);
    clang_cgf = new clang::CodeGen::CodeGenFunction(*clang_cgm);
    
    cT_int1  = clang_astcontext->BoolTy;
    cT_int8  = clang_astcontext->SignedCharTy;
    cT_uint8 = clang_astcontext->UnsignedCharTy;
    cT_int16 = clang_astcontext->ShortTy;
    cT_uint16 = clang_astcontext->UnsignedShortTy;
    cT_int32 = clang_astcontext->IntTy;
    cT_uint32 = clang_astcontext->UnsignedIntTy;
    cT_char = clang_astcontext->IntTy;
#ifdef __LP64__
    cT_int64 = clang_astcontext->LongTy;
    cT_uint64 = clang_astcontext->UnsignedLongTy;
#else
    cT_int64 = clang_astcontext->LongLongTy;
    cT_uint64 = clang_astcontext->UnsignedLongLongTy;
#endif
    cT_size = clang_astcontext->getSizeType();
    cT_int128 = clang_astcontext->Int128Ty;
    cT_uint128 = clang_astcontext->UnsignedInt128Ty;
    cT_complex64 = clang_astcontext->FloatComplexTy;
    cT_complex128 = clang_astcontext->DoubleComplexTy;

    cT_float32 = clang_astcontext->FloatTy;
    cT_float64 = clang_astcontext->DoubleTy;
    cT_void = clang_astcontext->VoidTy;

    cT_pvoid = clang_astcontext->getPointerType(cT_void);

    init_header("test2.h");
}

DLLEXPORT extern "C" void *setup_cpp_env(void *module, void *jlfunc, void *decl)
{
    const clang::Decl* MD = ((const clang::Decl *)decl);
    clang_astcontext = &MD->getASTContext();

    llvm::Function *w = (Function *)jlfunc;



    BasicBlock &b0 = w->getEntryBlock();

    // setup the environment to clang's expecations
    clang_cgf->Builder.SetInsertPoint( &b0 );
    // clang expects to alloca memory before the AllocaInsertPt
    // typically, clang would create this pointer when it started emitting the function
    // instead, we create a dummy reference here
    // for efficiency, we avoid creating a new placehold instruction if possible
    BasicBlock* alloca_bb = &b0;
    llvm::Instruction *alloca_bb_ptr = NULL;
    if (alloca_bb->empty()) {
        llvm::Value *Undef = llvm::UndefValue::get(T_int32);
        clang_cgf->AllocaInsertPt = alloca_bb_ptr = new llvm::BitCastInst(Undef, T_int32, "", alloca_bb);
    } else
        clang_cgf->AllocaInsertPt = &alloca_bb->front();

    clang_cgf->CurFn = w;

    return alloca_bb_ptr;
}

DLLEXPORT extern "C" void cleanup_cpp_env(void *alloca_bb_ptr, void *decl)
{
    // cleanup the environment
    clang_cgf->AllocaInsertPt = 0; // free this ptr reference
    if (alloca_bb_ptr)
        ((llvm::Instruction *)alloca_bb_ptr)->eraseFromParent();
}

DLLEXPORT extern "C" void emit_cpp_new(void *type)
{
    clang::Decl* MD = ((clang::Decl *)type);
    clang::TypeDecl* cdecl = dyn_cast<clang::TypeDecl>(MD);
    clang::FunctionDecl *OperatorNew = NULL;
    clang::FunctionDecl *OperatorDelete = NULL;

    clang::ASTContext &astctx = MD->getASTContext();
    clang_compiler->setASTContext(&astctx);

    bool globalNew = false;
    clang::QualType ty = clang::QualType(cdecl->getTypeForDecl(),0);

    clang::Sema &sema = clang_compiler->getSema();

    // TODO: This may be incorrect.
    sema.CurContext = MD->getDeclContext();

    sema.FindAllocationFunctions(clang::SourceLocation(),clang::SourceLocation(),globalNew,
    ty,false,NULL,0,OperatorNew,OperatorDelete);

    Value *ret = clang_cgf->EmitCXXNewExpr(dyn_cast<clang::CXXNewExpr>(sema.Owned(new (astctx) clang::CXXNewExpr(MD->getASTContext(),globalNew,OperatorNew,OperatorDelete,false,ArrayRef< clang::Expr * >(),
        clang::SourceRange(),
        NULL,                       //Array Size
        clang::CXXNewExpr::NoInit,  //Initialization Style
        NULL,                       //Initializer
        astctx.getPointerType(ty),  //Allocated Type
        NULL,                       //Type Source Info
        clang::SourceRange(),
        clang::SourceRange()
        )).get()));

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

DLLEXPORT extern "C" void *get_nth_argument(Function *f, size_t n)
{
    size_t i = 0;
    Function::arg_iterator AI = clang_cgf->CurFn->arg_begin();
    for (; AI != clang_cgf->CurFn->arg_end(); ++AI)
    {  
        if (i == n)
            return AI++;
        AI++;
    }
    return NULL;
}

DLLEXPORT extern "C" void *lookup_name(char *name, clang::Decl *decl)
{
    clang::Sema &sema = clang_compiler->getSema();
    clang::LookupResult R(sema, clang::DeclarationName(&clang_astcontext->Idents.get(name)), clang::SourceLocation(), clang::Sema::LookupAnyName);
    sema.LookupQualifiedName(R, dyn_cast<clang::DeclContext>(decl), false);
    return R.getAsSingle<clang::Decl>();
}

DLLEXPORT extern "C" void *lookup_toplevel_name(char *name, clang::Decl *decl)
{
    clang::Sema &sema = clang_compiler->getSema();
    clang::LookupResult R(sema, clang::DeclarationName(&clang_astcontext->Idents.get(name)), clang::SourceLocation(), clang::Sema::LookupAnyName);
    sema.LookupName(R, sema.TUScope, false);
    return R.getAsSingle<clang::Decl>();
}

DLLEXPORT extern "C" void *get_primary_dc(clang::DeclContext *dc)
{
    return dc->getPrimaryContext();
}

DLLEXPORT extern "C" void *decl_context(clang::Decl *decl)
{
    return dyn_cast<clang::DeclContext>(decl);
}

DLLEXPORT extern "C" void *to_decl(clang::DeclContext *decl)
{
    return dyn_cast<clang::Decl>(decl);
}


DLLEXPORT extern "C" void *get_result_type(void *cppfunc)
{
    clang::Decl* MD = ((clang::Decl *)cppfunc);
    clang::FunctionDecl* fdecl = dyn_cast<clang::FunctionDecl>(MD);
    return (void*)fdecl->getCallResultType().getTypePtr();
}

DLLEXPORT extern "C" void emit_cpp_call(void *cppfunc, Value **args, size_t nargs, bool Forward)
{
    clang::Decl* MD = ((clang::Decl *)cppfunc);
    clang::FunctionDecl* fdecl = dyn_cast<clang::FunctionDecl>(MD);

    clang::ASTContext &astctx = MD->getASTContext();

    const clang::CodeGen::CGFunctionInfo &cgfi = clang_cgt->arrangeFunctionDeclaration(fdecl);
    const clang::FunctionType *FT = fdecl->getType()->getAs<clang::FunctionType>();

    clang::DeclRefExpr *DRE =
    new (astctx) clang::DeclRefExpr(fdecl, false, fdecl->getType(), clang::VK_LValue, clang::SourceLocation());

    clang::ImplicitCastExpr *ICE = 
    clang::ImplicitCastExpr::Create(astctx, astctx.getPointerType(fdecl->getType()), clang::CK_FunctionToPointerDecay,
                             DRE, 0, clang::VK_RValue);


    // emit the actual call
    clang::CodeGen::ReturnValueSlot return_slot;
    clang::CodeGen::CallArgList argvals;
    clang::FunctionDecl::param_const_iterator it = fdecl->param_begin();
    if(Forward)
    {
        Function::arg_iterator AI = clang_cgf->CurFn->arg_begin();
        if(isa<clang::CXXMethodDecl>(fdecl))
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
        for (size_t i = 0; i < nargs; ++i, ++it)
            argvals.add(clang::CodeGen::RValue::get(args[i]),(*it)->getOriginalType());
    }

    // emit default arguments
    for(; it != fdecl->param_end(); ++it)
    {
        assert((*it)->hasDefaultArg());
        argvals.add(clang_cgf->EmitAnyExpr((*it)->getDefaultArg()),(*it)->getOriginalType());
    }

    clang::Sema &sema = clang_compiler->getSema();

    llvm::FunctionType *Ty = clang_cgm->getTypes().GetFunctionType(cgfi);
    clang::CodeGen::RValue rv;
    sema.MarkFunctionReferenced(clang::SourceLocation(),fdecl);
    if(isa<clang::CXXMethodDecl>(fdecl))
    {
        clang::CXXMethodDecl *cxx = dyn_cast<clang::CXXMethodDecl>(fdecl);

        // Well, let's try this, shall we?
        if (cxx->doesThisDeclarationHaveABody())
            clang_cgm->EmitTopLevelDecl(cxx);

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
    // Funnily the RetVoid won't actually be inserted into the basic block
    // of the function if ret == NULL. Instead clan
    if (ret == NULL || ret->getType() == T_void)
        clang_cgf->Builder.CreateRetVoid();
    else
        clang_cgf->Builder.CreateRet(clang_cgf->Builder.CreateBitCast(ret,clang_cgf->CurFn->getReturnType()));

    clang_cgm->Release();
    sema.PerformPendingInstantiations();
}

DLLEXPORT extern "C" void *clang_get_instance()
{
    return clang_compiler;
}

DLLEXPORT extern "C" void *clang_get_cgm()
{
    return clang_cgm;
}

DLLEXPORT extern "C" void *clang_get_cgf()
{
    return clang_cgf;
}

DLLEXPORT extern "C" void *clang_get_cgt()
{
    return clang_cgt;
}

