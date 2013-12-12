// clang state
#undef B0 //rom termios
#include "llvm/ADT/DenseMapInfo.h"
#include "llvm/Bitcode/ReaderWriter.h"
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
#include "CodeGen/CodeGenModule.h"
#include <CodeGen/CodeGenTypes.h>
#include <CodeGen/CodeGenFunction.h>

static clang::ASTContext *clang_astcontext;
static clang::CompilerInstance *clang_compiler;
static clang::CodeGen::CodeGenModule *clang_cgm;
static clang::CodeGen::CodeGenTypes *clang_cgt;
static clang::CodeGen::CodeGenFunction *clang_cgf;
static DataLayout *TD;

static llvm::Module *shadow_module;

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
DLLEXPORT void init_header(char *name)
{
    clang::FileManager &fm = clang_compiler->getFileManager();
    clang::Preprocessor &pp = clang_compiler->getPreprocessor();
    clang::HeaderSearchOptions &opts = pp.getHeaderSearchInfo().getHeaderSearchOpts();
    opts.UseBuiltinIncludes = 1;
    opts.UseStandardSystemIncludes = 1;
    opts.UseStandardCXXIncludes = 1;
    pp.getHeaderSearchInfo().AddSearchPath(clang::DirectoryLookup(fm.getDirectory("/usr/include/c++/4.8"),clang::SrcMgr::C_System,false),true);
    pp.getHeaderSearchInfo().AddSearchPath(clang::DirectoryLookup(fm.getDirectory("/usr/include/x86_64-linux-gnu/c++/4.8/"),clang::SrcMgr::C_System,false),true);
    pp.getHeaderSearchInfo().AddSearchPath(clang::DirectoryLookup(fm.getDirectory("/home/kfischer/julia/usr/lib/clang/3.5/include/"),clang::SrcMgr::C_System,false),true);
    #define DIR(X) pp.getHeaderSearchInfo().AddSearchPath(clang::DirectoryLookup(fm.getDirectory(X),clang::SrcMgr::C_User,false),false);
    DIR("/home/kfischer/julia/src/support")
    DIR("/home/kfischer/julia/usr/include")
    DIR("/home/kfischer/julia/deps/llvm-svn/tools/clang/")
    DIR("/home/kfischer/julia/deps/llvm-svn/tools/clang/include/")
    clang_compiler->getDiagnosticClient().BeginSourceFile(clang_compiler->getLangOpts(), 0);
    pp.getBuiltinInfo().InitializeBuiltins(pp.getIdentifierTable(),
                                           clang_compiler->getLangOpts());
    pp.enableIncrementalProcessing();
    clang::FrontendInputFile fi = clang::FrontendInputFile(name,clang::IK_CXX);
    clang_compiler->InitializeSourceManager(fi);
    clang::ParseAST(clang_compiler->getSema());
}

DLLEXPORT void init_julia_clang_env(void *module) {
    //copied from http://www.ibm.com/developerworks/library/os-createcompilerllvm2/index.html
    clang_compiler = new clang::CompilerInstance;
    clang_compiler->createDiagnostics();
    clang_compiler->getLangOpts().CPlusPlus = 1;
    clang_compiler->getLangOpts().LineComment = 1;
    clang_compiler->getLangOpts().Bool = 1;
    clang_compiler->getLangOpts().WChar = 1;
    clang_compiler->getLangOpts().C99 = 1;
    clang_compiler->getLangOpts().ImplicitInt = 0;
    clang_compiler->getTargetOpts().Triple = "x86_64-apple-darwin12.4.0";
    clang::TargetInfo *tin = clang::TargetInfo::CreateTargetInfo(clang_compiler->getDiagnostics(), &clang_compiler->getTargetOpts());
    clang_compiler->setTarget(tin);
    clang_compiler->createFileManager();
    clang_compiler->createSourceManager(clang_compiler->getFileManager());
    clang_compiler->createPreprocessor();
    clang_compiler->createASTContext();
    shadow_module = new llvm::Module("clangShadow",((llvm::Module*)module)->getContext());
    clang_astcontext = &clang_compiler->getASTContext();
    clang_compiler->setASTConsumer(new JuliaCodeGenerator());
    clang_compiler->createSema(clang::TU_Prefix,NULL);
    TD = new DataLayout(tin->getTargetDescription());
    clang_cgm = new clang::CodeGen::CodeGenModule(
        *clang_astcontext,
        clang_compiler->getCodeGenOpts(),
        *shadow_module,
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
}

static llvm::Module *cur_module = NULL;
static llvm::Function *cur_func = NULL;


DLLEXPORT void *setup_cpp_env(void *module, void *jlfunc)
{
    llvm::Function *w = (Function *)jlfunc;
    assert(w != NULL);
    assert(clang_cgf != NULL);
    cur_module = (llvm::Module*)module;
    cur_func = w;

    Function *ShadowF = Function::Create(w->getFunctionType(),
        Function::ExternalLinkage,
        w->getName(),
        shadow_module);    

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

    return alloca_bb_ptr;
}

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
}

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

DLLEXPORT void cleanup_cpp_env(void *alloca_bb_ptr)
{
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
    if (alloca_bb_ptr)
        ((llvm::Instruction *)alloca_bb_ptr)->eraseFromParent(); 

    copy_into(F,cur_func);

    F->eraseFromParent();
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

    Value *ret = clang_cgf->EmitCXXNewExpr(dyn_cast<clang::CXXNewExpr>(sema.Owned(new (astctx) clang::CXXNewExpr(MD->getASTContext(),globalNew,OperatorNew,OperatorDelete,false,ArrayRef< clang::Expr * >(),
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


DLLEXPORT void *get_result_type(void *cppfunc)
{
    clang::Decl* MD = ((clang::Decl *)cppfunc);
    clang::FunctionDecl* fdecl = dyn_cast<clang::FunctionDecl>(MD);
    return (void*)fdecl->getResultType().getTypePtr();
}

DLLEXPORT void *emit_field_ref(clang::Type *BaseType, Value *BaseVal, clang::FieldDecl *FieldDecl)
{
    clang::CodeGen::LValue BaseLV = clang_cgf->MakeNaturalAlignAddrLValue(BaseVal,clang::QualType(BaseType,0));
    clang::CodeGen::LValue LV = clang_cgf->EmitLValueForField(BaseLV,FieldDecl);
    return LV.getAddress();
}

DLLEXPORT Value *emit_cpp_call(void *cppfunc, Value **args, size_t nargs, bool Forward, bool EmitReturn)
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
        size_t i = 0;
        if(isa<clang::CXXMethodDecl>(fdecl))
        {
            clang::CXXMethodDecl *cxx = dyn_cast<clang::CXXMethodDecl>(fdecl);
            if(!cxx->isStatic())
                argvals.add(clang::CodeGen::RValue::get(args[i++]),cxx->getThisType(astctx));
        }
        for (; i < nargs; ++i, ++it)
            argvals.add(clang::CodeGen::RValue::get(args[i]),(*it)->getOriginalType());
    }

    clang::Sema &sema = clang_compiler->getSema();

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

DLLEXPORT void cdump(void *decl)
{
    ((clang::Decl*) decl)->dump();
}


// PDB specific functions
DLLEXPORT llvm::Module *pdb_load_module(char *file)
{
    OwningPtr< MemoryBuffer > membuf;
    MemoryBuffer::getFile(file,membuf);
    if (membuf.get() == NULL)
        return NULL;
    return ParseBitcodeFile(membuf.get(),shadow_module->getContext());
}

DLLEXPORT void *pdb_lookup_function(llvm::Module *mod, char *name)
{
    return mod->getFunction(name);
}

DLLEXPORT unsigned int32_clang_type()
{
    return clang::BuiltinType::UInt;
}


}
