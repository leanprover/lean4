// Lean compiler output
// Module: Lean.Compiler.LCNF.ToImpure
// Imports: import Lean.Compiler.LCNF.ToImpureType public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.PhaseExt import Init.Data.Format.Macro
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Compiler_LCNF_toImpureType(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isVoid(lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_getCtorLayout(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CtorFieldInfo_spillDepth(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_spillLinkIdx;
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedLetDecl_default___redArg();
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t, lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Compiler_LCNF_nameToImpureType(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_numSpillObjs(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_spillCtorInfo(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CtorInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tagged_return"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(42, 116, 83, 63, 133, 144, 27, 22)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "mark extern definition to always return tagged values"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToImpure"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(104, 151, 203, 144, 27, 18, 236, 68)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(65, 46, 141, 239, 133, 91, 141, 199)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(228, 234, 69, 211, 145, 232, 229, 254)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 187, 249, 147, 190, 91, 90, 40)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(183, 4, 28, 224, 230, 52, 114, 252)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "taggedReturnAttr"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 95, 219, 231, 93, 109, 209, 250)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 149, .m_capacity = 149, .m_length = 148, .m_data = "Marks an extern definition to be guaranteed to always return tagged values.\nThis information is used to optimize reference counting in the compiler."};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(18) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(93) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(93) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_liftIOCore___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_get___boxed, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_spill"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 149, 131, 37, 1, 72, 252, 34)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "obj"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(240, 235, 44, 74, 242, 121, 239, 90)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lcErased"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 218, 234, 194, 194, 57, 75, 5)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lcVoid"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7_value),LEAN_SCALAR_PTR_LITERAL(68, 180, 59, 167, 252, 217, 37, 174)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.ToImpure"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "_private.Lean.Compiler.LCNF.ToImpure.0.Lean.Compiler.LCNF.lowerResultType.resultTypeForArity"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invalid arity"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tagged"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 57, 252, 162, 142, 133, 51, 193)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "projection of non-structure type"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "_private.Lean.Compiler.LCNF.ToImpure.0.Lean.Compiler.LCNF.lowerLet"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "overap"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "reference to unbound name"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "ToImpure: unexpected use of noncomputable declaration `"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`; please report this issue"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9;
static const lean_array_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "code generator does not support recursor `"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "` yet, consider using 'match ... with' and/or structural recursion"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 38, .m_data = "all local functions should be λ-lifted"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Lean.Compiler.LCNF.ToImpure.0.Lean.Compiler.LCNF.Code.toImpure"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2;
static const lean_array_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "assertion violation: c.alts.size == 1\n      "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: ctorName == info.ctorName\n      "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "assertion violation: info.fieldIdx < ps.size\n      "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "mismatched fields and params"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "_private.Lean.Compiler.LCNF.ToImpure.0.Lean.Compiler.LCNF.Alt.toImpure.loop"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Error while compiling function '"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "': @[tagged_return] is only valid for extern declarations"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "@[tagged_return] on function '"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' with scalar return type "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_toImpure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_toImpure___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_toImpure___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_toImpure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toImpure"};
static const lean_object* l_Lean_Compiler_LCNF_toImpure___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_toImpure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(136, 181, 13, 187, 73, 36, 105, 247)}};
static const lean_object* l_Lean_Compiler_LCNF_toImpure___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_toImpure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 2, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_toImpure___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_toImpure = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(198, 36, 7, 136, 133, 159, 176, 55)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 198, 164, 214, 24, 238, 231, 213)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 168, 178, 247, 202, 119, 73, 243)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(202, 77, 105, 21, 218, 121, 239, 197)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 184, 169, 248, 178, 143, 79, 195)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 14, 162, 97, 10, 113, 167, 163)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 160, 236, 105, 16, 144, 54, 23)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)(((size_t)(6355896) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(233, 87, 80, 162, 250, 65, 116, 159)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 254, 170, 235, 80, 165, 179, 171)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 19, 111, 73, 147, 106, 206, 64)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(135, 181, 11, 188, 89, 247, 207, 91)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object* v_x_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(v_x_7_, v___y_8_, v___y_9_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v_x_7_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; lean_object* v___x_61_; 
v___f_54_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_55_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_56_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_57_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_58_ = 0;
v___x_59_ = lean_box(2);
v___x_60_ = 0;
v___x_61_ = l_Lean_registerTagAttribute(v___x_55_, v___x_56_, v___f_54_, v___x_57_, v___x_58_, v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1(){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_67_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0));
v___x_68_ = l_Lean_addBuiltinDocString(v___x_66_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___boxed(lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3(){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_98_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6));
v___x_99_ = l_Lean_addBuiltinDeclarationRanges(v___x_97_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___boxed(lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3();
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(lean_object* v_____do__lift_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_subst_109_; lean_object* v___x_110_; 
v_subst_109_ = lean_ctor_get(v_____do__lift_102_, 0);
lean_inc_ref(v_subst_109_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v_subst_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed(lean_object* v_____do__lift_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(v_____do__lift_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v_____do__lift_111_);
return v_res_118_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_instMonadEIO___redArg();
return v___x_119_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0);
v___x_121_ = l_StateRefT_x27_instMonad___redArg(v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue(void){
_start:
{
lean_object* v___x_150_; lean_object* v_toApplicative_151_; lean_object* v_toFunctor_152_; lean_object* v_toSeq_153_; lean_object* v_toSeqLeft_154_; lean_object* v_toSeqRight_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_toApplicative_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_197_; 
v___x_150_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_151_ = lean_ctor_get(v___x_150_, 0);
v_toFunctor_152_ = lean_ctor_get(v_toApplicative_151_, 0);
v_toSeq_153_ = lean_ctor_get(v_toApplicative_151_, 2);
v_toSeqLeft_154_ = lean_ctor_get(v_toApplicative_151_, 3);
v_toSeqRight_155_ = lean_ctor_get(v_toApplicative_151_, 4);
v___f_156_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_157_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref_n(v_toFunctor_152_, 2);
v___f_158_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_158_, 0, v_toFunctor_152_);
v___f_159_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_159_, 0, v_toFunctor_152_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___f_158_);
lean_ctor_set(v___x_160_, 1, v___f_159_);
lean_inc(v_toSeqRight_155_);
v___f_161_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_161_, 0, v_toSeqRight_155_);
lean_inc(v_toSeqLeft_154_);
v___f_162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_162_, 0, v_toSeqLeft_154_);
lean_inc(v_toSeq_153_);
v___f_163_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_163_, 0, v_toSeq_153_);
v___x_164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_164_, 0, v___x_160_);
lean_ctor_set(v___x_164_, 1, v___f_156_);
lean_ctor_set(v___x_164_, 2, v___f_163_);
lean_ctor_set(v___x_164_, 3, v___f_162_);
lean_ctor_set(v___x_164_, 4, v___f_161_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___f_157_);
v___x_166_ = l_StateRefT_x27_instMonad___redArg(v___x_165_);
v_toApplicative_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_197_ == 0)
{
lean_object* v_unused_198_; 
v_unused_198_ = lean_ctor_get(v___x_166_, 1);
lean_dec(v_unused_198_);
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_197_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_toApplicative_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_197_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v_toFunctor_171_; lean_object* v_toSeq_172_; lean_object* v_toSeqLeft_173_; lean_object* v_toSeqRight_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_195_; 
v_toFunctor_171_ = lean_ctor_get(v_toApplicative_167_, 0);
v_toSeq_172_ = lean_ctor_get(v_toApplicative_167_, 2);
v_toSeqLeft_173_ = lean_ctor_get(v_toApplicative_167_, 3);
v_toSeqRight_174_ = lean_ctor_get(v_toApplicative_167_, 4);
v_isSharedCheck_195_ = !lean_is_exclusive(v_toApplicative_167_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v_toApplicative_167_, 1);
lean_dec(v_unused_196_);
v___x_176_ = v_toApplicative_167_;
v_isShared_177_ = v_isSharedCheck_195_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_toSeqRight_174_);
lean_inc(v_toSeqLeft_173_);
lean_inc(v_toSeq_172_);
lean_inc(v_toFunctor_171_);
lean_dec(v_toApplicative_167_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_195_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___f_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___x_183_; lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___x_188_; 
v___f_178_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4));
v___f_179_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_180_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_171_);
v___f_181_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_181_, 0, v_toFunctor_171_);
v___f_182_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_182_, 0, v_toFunctor_171_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___f_181_);
lean_ctor_set(v___x_183_, 1, v___f_182_);
v___f_184_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_184_, 0, v_toSeqRight_174_);
v___f_185_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_185_, 0, v_toSeqLeft_173_);
v___f_186_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_186_, 0, v_toSeq_172_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v___f_184_);
lean_ctor_set(v___x_176_, 3, v___f_185_);
lean_ctor_set(v___x_176_, 2, v___f_186_);
lean_ctor_set(v___x_176_, 1, v___f_179_);
lean_ctor_set(v___x_176_, 0, v___x_183_);
v___x_188_ = v___x_176_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v___f_179_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v___f_186_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v___f_185_);
lean_ctor_set(v_reuseFailAlloc_194_, 4, v___f_184_);
v___x_188_ = v_reuseFailAlloc_194_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 1, v___f_180_);
lean_ctor_set(v___x_169_, 0, v___x_188_);
v___x_190_ = v___x_169_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___f_180_);
v___x_190_ = v_reuseFailAlloc_193_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18));
v___x_192_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_192_, 0, lean_box(0));
lean_closure_set(v___x_192_, 1, lean_box(0));
lean_closure_set(v___x_192_, 2, v___x_190_);
lean_closure_set(v___x_192_, 3, lean_box(0));
lean_closure_set(v___x_192_, 4, lean_box(0));
lean_closure_set(v___x_192_, 5, v___x_191_);
lean_closure_set(v___x_192_, 6, v___f_178_);
return v___x_192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(lean_object* v_f_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; lean_object* v_subst_207_; lean_object* v_jpParamMask_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_219_; 
v___x_206_ = lean_st_ref_take(v___y_200_);
v_subst_207_ = lean_ctor_get(v___x_206_, 0);
v_jpParamMask_208_ = lean_ctor_get(v___x_206_, 1);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_219_ == 0)
{
v___x_210_ = v___x_206_;
v_isShared_211_ = v_isSharedCheck_219_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_jpParamMask_208_);
lean_inc(v_subst_207_);
lean_dec(v___x_206_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_219_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_212_ = lean_box(0);
v___x_213_ = lean_apply_1(v_f_199_, v_subst_207_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_213_);
v___x_215_ = v___x_210_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_jpParamMask_208_);
v___x_215_ = v_reuseFailAlloc_218_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_st_ref_put(v___y_200_, v___x_215_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_212_);
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed(lean_object* v_f_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(v_f_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(lean_object* v_a_230_, lean_object* v_b_231_, lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_232_) == 0)
{
lean_dec(v_b_231_);
lean_dec(v_a_230_);
return v_x_232_;
}
else
{
lean_object* v_key_233_; lean_object* v_value_234_; lean_object* v_tail_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_247_; 
v_key_233_ = lean_ctor_get(v_x_232_, 0);
v_value_234_ = lean_ctor_get(v_x_232_, 1);
v_tail_235_ = lean_ctor_get(v_x_232_, 2);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_232_);
if (v_isSharedCheck_247_ == 0)
{
v___x_237_ = v_x_232_;
v_isShared_238_ = v_isSharedCheck_247_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_tail_235_);
lean_inc(v_value_234_);
lean_inc(v_key_233_);
lean_dec(v_x_232_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_247_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
uint8_t v___x_239_; 
v___x_239_ = l_Lean_instBEqFVarId_beq(v_key_233_, v_a_230_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_230_, v_b_231_, v_tail_235_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 2, v___x_240_);
v___x_242_ = v___x_237_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_key_233_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_value_234_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
else
{
lean_object* v___x_245_; 
lean_dec(v_value_234_);
lean_dec(v_key_233_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_b_231_);
lean_ctor_set(v___x_237_, 0, v_a_230_);
v___x_245_ = v___x_237_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_230_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_b_231_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_tail_235_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
return v_x_248_;
}
else
{
lean_object* v_key_250_; lean_object* v_value_251_; lean_object* v_tail_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_275_; 
v_key_250_ = lean_ctor_get(v_x_249_, 0);
v_value_251_ = lean_ctor_get(v_x_249_, 1);
v_tail_252_ = lean_ctor_get(v_x_249_, 2);
v_isSharedCheck_275_ = !lean_is_exclusive(v_x_249_);
if (v_isSharedCheck_275_ == 0)
{
v___x_254_ = v_x_249_;
v_isShared_255_ = v_isSharedCheck_275_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_tail_252_);
lean_inc(v_value_251_);
lean_inc(v_key_250_);
lean_dec(v_x_249_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_275_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; uint64_t v___x_259_; uint64_t v_fold_260_; uint64_t v___x_261_; uint64_t v___x_262_; uint64_t v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; size_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_256_ = lean_array_get_size(v_x_248_);
v___x_257_ = l_Lean_instHashableFVarId_hash(v_key_250_);
v___x_258_ = 32ULL;
v___x_259_ = lean_uint64_shift_right(v___x_257_, v___x_258_);
v_fold_260_ = lean_uint64_xor(v___x_257_, v___x_259_);
v___x_261_ = 16ULL;
v___x_262_ = lean_uint64_shift_right(v_fold_260_, v___x_261_);
v___x_263_ = lean_uint64_xor(v_fold_260_, v___x_262_);
v___x_264_ = lean_uint64_to_usize(v___x_263_);
v___x_265_ = lean_usize_of_nat(v___x_256_);
v___x_266_ = ((size_t)1ULL);
v___x_267_ = lean_usize_sub(v___x_265_, v___x_266_);
v___x_268_ = lean_usize_land(v___x_264_, v___x_267_);
v___x_269_ = lean_array_uget_borrowed(v_x_248_, v___x_268_);
lean_inc(v___x_269_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 2, v___x_269_);
v___x_271_ = v___x_254_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_key_250_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_value_251_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v___x_269_);
v___x_271_ = v_reuseFailAlloc_274_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; 
v___x_272_ = lean_array_uset(v_x_248_, v___x_268_, v___x_271_);
v_x_248_ = v___x_272_;
v_x_249_ = v_tail_252_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(lean_object* v_i_276_, lean_object* v_source_277_, lean_object* v_target_278_){
_start:
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_array_get_size(v_source_277_);
v___x_280_ = lean_nat_dec_lt(v_i_276_, v___x_279_);
if (v___x_280_ == 0)
{
lean_dec_ref(v_source_277_);
lean_dec(v_i_276_);
return v_target_278_;
}
else
{
lean_object* v_es_281_; lean_object* v___x_282_; lean_object* v_source_283_; lean_object* v_target_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_es_281_ = lean_array_fget(v_source_277_, v_i_276_);
v___x_282_ = lean_box(0);
v_source_283_ = lean_array_fset(v_source_277_, v_i_276_, v___x_282_);
v_target_284_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_target_278_, v_es_281_);
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_add(v_i_276_, v___x_285_);
lean_dec(v_i_276_);
v_i_276_ = v___x_286_;
v_source_277_ = v_source_283_;
v_target_278_ = v_target_284_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(lean_object* v_data_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_nbuckets_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_289_ = lean_array_get_size(v_data_288_);
v___x_290_ = lean_unsigned_to_nat(2u);
v_nbuckets_291_ = lean_nat_mul(v___x_289_, v___x_290_);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_box(0);
v___x_294_ = lean_mk_array(v_nbuckets_291_, v___x_293_);
v___x_295_ = lean_array_propagate_mark(v_data_288_, v___x_294_);
v___x_296_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v___x_292_, v_data_288_, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(lean_object* v_a_297_, lean_object* v_x_298_){
_start:
{
if (lean_obj_tag(v_x_298_) == 0)
{
uint8_t v___x_299_; 
v___x_299_ = 0;
return v___x_299_;
}
else
{
lean_object* v_key_300_; lean_object* v_tail_301_; uint8_t v___x_302_; 
v_key_300_ = lean_ctor_get(v_x_298_, 0);
v_tail_301_ = lean_ctor_get(v_x_298_, 2);
v___x_302_ = l_Lean_instBEqFVarId_beq(v_key_300_, v_a_297_);
if (v___x_302_ == 0)
{
v_x_298_ = v_tail_301_;
goto _start;
}
else
{
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg___boxed(lean_object* v_a_304_, lean_object* v_x_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_304_, v_x_305_);
lean_dec(v_x_305_);
lean_dec(v_a_304_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(lean_object* v_m_308_, lean_object* v_a_309_, lean_object* v_b_310_){
_start:
{
lean_object* v_size_311_; lean_object* v_buckets_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_355_; 
v_size_311_ = lean_ctor_get(v_m_308_, 0);
v_buckets_312_ = lean_ctor_get(v_m_308_, 1);
v_isSharedCheck_355_ = !lean_is_exclusive(v_m_308_);
if (v_isSharedCheck_355_ == 0)
{
v___x_314_ = v_m_308_;
v_isShared_315_ = v_isSharedCheck_355_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_buckets_312_);
lean_inc(v_size_311_);
lean_dec(v_m_308_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_355_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; uint64_t v___x_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v_fold_320_; uint64_t v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; size_t v___x_327_; size_t v___x_328_; lean_object* v_bkt_329_; uint8_t v___x_330_; 
v___x_316_ = lean_array_get_size(v_buckets_312_);
v___x_317_ = l_Lean_instHashableFVarId_hash(v_a_309_);
v___x_318_ = 32ULL;
v___x_319_ = lean_uint64_shift_right(v___x_317_, v___x_318_);
v_fold_320_ = lean_uint64_xor(v___x_317_, v___x_319_);
v___x_321_ = 16ULL;
v___x_322_ = lean_uint64_shift_right(v_fold_320_, v___x_321_);
v___x_323_ = lean_uint64_xor(v_fold_320_, v___x_322_);
v___x_324_ = lean_uint64_to_usize(v___x_323_);
v___x_325_ = lean_usize_of_nat(v___x_316_);
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_sub(v___x_325_, v___x_326_);
v___x_328_ = lean_usize_land(v___x_324_, v___x_327_);
v_bkt_329_ = lean_array_uget_borrowed(v_buckets_312_, v___x_328_);
v___x_330_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_309_, v_bkt_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v_size_x27_332_; lean_object* v___x_333_; lean_object* v_buckets_x27_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v_size_x27_332_ = lean_nat_add(v_size_311_, v___x_331_);
lean_dec(v_size_311_);
lean_inc(v_bkt_329_);
v___x_333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_333_, 0, v_a_309_);
lean_ctor_set(v___x_333_, 1, v_b_310_);
lean_ctor_set(v___x_333_, 2, v_bkt_329_);
v_buckets_x27_334_ = lean_array_uset(v_buckets_312_, v___x_328_, v___x_333_);
v___x_335_ = lean_unsigned_to_nat(4u);
v___x_336_ = lean_nat_mul(v_size_x27_332_, v___x_335_);
v___x_337_ = lean_unsigned_to_nat(3u);
v___x_338_ = lean_nat_div(v___x_336_, v___x_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_array_get_size(v_buckets_x27_334_);
v___x_340_ = lean_nat_dec_le(v___x_338_, v___x_339_);
lean_dec(v___x_338_);
if (v___x_340_ == 0)
{
lean_object* v_val_341_; lean_object* v___x_343_; 
v_val_341_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_buckets_x27_334_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v_val_341_);
lean_ctor_set(v___x_314_, 0, v_size_x27_332_);
v___x_343_ = v___x_314_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_size_x27_332_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_val_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
else
{
lean_object* v___x_346_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v_buckets_x27_334_);
lean_ctor_set(v___x_314_, 0, v_size_x27_332_);
v___x_346_ = v___x_314_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_size_x27_332_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_buckets_x27_334_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v___x_348_; lean_object* v_buckets_x27_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
lean_inc(v_bkt_329_);
v___x_348_ = lean_box(0);
v_buckets_x27_349_ = lean_array_uset(v_buckets_312_, v___x_328_, v___x_348_);
v___x_350_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_309_, v_b_310_, v_bkt_329_);
v___x_351_ = lean_array_uset(v_buckets_x27_349_, v___x_328_, v___x_350_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v___x_351_);
v___x_353_ = v___x_314_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_size_311_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(lean_object* v_p_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_fvarId_362_; lean_object* v_binderName_363_; lean_object* v_type_364_; uint8_t v_borrow_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_420_; 
v_fvarId_362_ = lean_ctor_get(v_p_356_, 0);
v_binderName_363_ = lean_ctor_get(v_p_356_, 1);
v_type_364_ = lean_ctor_get(v_p_356_, 2);
v_borrow_365_ = lean_ctor_get_uint8(v_p_356_, sizeof(void*)*3);
v_isSharedCheck_420_ = !lean_is_exclusive(v_p_356_);
if (v_isSharedCheck_420_ == 0)
{
v___x_367_ = v_p_356_;
v_isShared_368_ = v_isSharedCheck_420_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_type_364_);
lean_inc(v_binderName_363_);
lean_inc(v_fvarId_362_);
lean_dec(v_p_356_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_420_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Compiler_LCNF_toImpureType(v_type_364_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_411_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_411_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_411_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_411_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___y_375_; uint8_t v___x_409_; 
v___x_409_ = l_Lean_Expr_isVoid(v_a_370_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; 
v___x_410_ = l_Lean_Expr_isErased(v_a_370_);
if (v___x_410_ == 0)
{
v___y_375_ = v_a_358_;
goto v___jp_374_;
}
else
{
goto v___jp_395_;
}
}
else
{
goto v___jp_395_;
}
v___jp_374_:
{
uint8_t v___x_376_; lean_object* v___x_378_; 
v___x_376_ = 1;
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 2, v_a_370_);
v___x_378_ = v___x_367_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_fvarId_362_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_binderName_363_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_a_370_);
lean_ctor_set_uint8(v_reuseFailAlloc_394_, sizeof(void*)*3, v_borrow_365_);
v___x_378_ = v_reuseFailAlloc_394_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; lean_object* v_lctx_380_; lean_object* v_nextIdx_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_393_; 
v___x_379_ = lean_st_ref_take(v___y_375_);
v_lctx_380_ = lean_ctor_get(v___x_379_, 0);
v_nextIdx_381_ = lean_ctor_get(v___x_379_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_393_ == 0)
{
v___x_383_ = v___x_379_;
v_isShared_384_ = v_isSharedCheck_393_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_nextIdx_381_);
lean_inc(v_lctx_380_);
lean_dec(v___x_379_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_393_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
lean_inc_ref(v___x_378_);
v___x_385_ = l_Lean_Compiler_LCNF_LCtx_addParam(v___x_376_, v_lctx_380_, v___x_378_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_385_);
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_nextIdx_381_);
v___x_387_ = v_reuseFailAlloc_392_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_st_ref_put(v___y_375_, v___x_387_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_378_);
v___x_390_ = v___x_372_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_378_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
v___jp_395_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_subst_398_; lean_object* v_jpParamMask_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_408_; 
v___x_396_ = lean_box(0);
v___x_397_ = lean_st_ref_take(v_a_357_);
v_subst_398_ = lean_ctor_get(v___x_397_, 0);
v_jpParamMask_399_ = lean_ctor_get(v___x_397_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_408_ == 0)
{
v___x_401_ = v___x_397_;
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_jpParamMask_399_);
lean_inc(v_subst_398_);
lean_dec(v___x_397_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_405_; 
lean_inc(v_fvarId_362_);
v___x_403_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_398_, v_fvarId_362_, v___x_396_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_403_);
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_jpParamMask_399_);
v___x_405_ = v_reuseFailAlloc_407_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; 
v___x_406_ = lean_st_ref_put(v_a_357_, v___x_405_);
v___y_375_ = v_a_358_;
goto v___jp_374_;
}
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_del_object(v___x_367_);
lean_dec(v_binderName_363_);
lean_dec(v_fvarId_362_);
v_a_412_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_369_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_369_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg___boxed(lean_object* v_p_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec(v_a_422_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(lean_object* v_p_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_428_, v_a_429_, v_a_431_, v_a_432_, v_a_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___boxed(lean_object* v_p_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(v_p_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(lean_object* v_00_u03b2_444_, lean_object* v_m_445_, lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_m_445_, v_a_446_, v_b_447_);
return v___x_448_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(lean_object* v_00_u03b2_449_, lean_object* v_a_450_, lean_object* v_x_451_){
_start:
{
uint8_t v___x_452_; 
v___x_452_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_450_, v_x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___boxed(lean_object* v_00_u03b2_453_, lean_object* v_a_454_, lean_object* v_x_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(v_00_u03b2_453_, v_a_454_, v_x_455_);
lean_dec(v_x_455_);
lean_dec(v_a_454_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1(lean_object* v_00_u03b2_458_, lean_object* v_data_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_data_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2(lean_object* v_00_u03b2_461_, lean_object* v_a_462_, lean_object* v_b_463_, lean_object* v_x_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_462_, v_b_463_, v_x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_466_, lean_object* v_i_467_, lean_object* v_source_468_, lean_object* v_target_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v_i_467_, v_source_468_, v_target_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_471_, lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_x_472_, v_x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_box(0);
v___x_482_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__3));
v___x_483_ = l_Lean_Expr_const___override(v___x_482_, v___x_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg(lean_object* v_upperBound_484_, lean_object* v_a_485_, lean_object* v_b_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
uint8_t v___x_492_; 
v___x_492_ = lean_nat_dec_lt(v_a_485_, v_upperBound_484_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
lean_dec(v_a_485_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v_b_486_);
return v___x_493_;
}
else
{
lean_object* v_fst_494_; lean_object* v_snd_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_532_; 
v_fst_494_ = lean_ctor_get(v_b_486_, 0);
v_snd_495_ = lean_ctor_get(v_b_486_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v_b_486_);
if (v_isSharedCheck_532_ == 0)
{
v___x_497_ = v_b_486_;
v_isShared_498_ = v_isSharedCheck_532_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_snd_495_);
lean_inc(v_fst_494_);
lean_dec(v_b_486_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_532_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__1));
v___x_500_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_499_, v___y_488_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; uint8_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v___x_502_ = 1;
v___x_503_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4);
v___x_504_ = l_Lean_Compiler_LCNF_spillLinkIdx;
v___x_505_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v_snd_495_);
v___x_506_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_502_, v_a_501_, v___x_503_, v___x_505_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v_fvarId_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v_fvarId_508_ = lean_ctor_get(v_a_507_, 0);
lean_inc(v_fvarId_508_);
v___x_509_ = lean_array_push(v_fst_494_, v_a_507_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v_fvarId_508_);
lean_ctor_set(v___x_497_, 0, v___x_509_);
v___x_511_ = v___x_497_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_fvarId_508_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_nat_add(v_a_485_, v___x_512_);
lean_dec(v_a_485_);
v_a_485_ = v___x_513_;
v_b_486_ = v___x_511_;
goto _start;
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_del_object(v___x_497_);
lean_dec(v_fst_494_);
lean_dec(v_a_485_);
v_a_516_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_506_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_506_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_del_object(v___x_497_);
lean_dec(v_snd_495_);
lean_dec(v_fst_494_);
lean_dec(v_a_485_);
v_a_524_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_500_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_500_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___boxed(lean_object* v_upperBound_533_, lean_object* v_a_534_, lean_object* v_b_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg(v_upperBound_533_, v_a_534_, v_b_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v_upperBound_533_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs(lean_object* v_base_544_, lean_object* v_depth_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___x_551_; lean_object* v_decls_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_551_ = lean_unsigned_to_nat(0u);
v_decls_552_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs___closed__0));
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v_decls_552_);
lean_ctor_set(v___x_553_, 1, v_base_544_);
v___x_554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg(v_depth_545_, v___x_551_, v___x_553_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_563_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_fst_559_; lean_object* v___x_561_; 
v_fst_559_ = lean_ctor_get(v_a_555_, 0);
lean_inc(v_fst_559_);
lean_dec(v_a_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v_fst_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_fst_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_a_564_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_554_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_554_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs___boxed(lean_object* v_base_572_, lean_object* v_depth_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs(v_base_572_, v_depth_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_depth_573_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0(lean_object* v_upperBound_580_, lean_object* v_inst_581_, lean_object* v_R_582_, lean_object* v_a_583_, lean_object* v_b_584_, lean_object* v_c_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg(v_upperBound_580_, v_a_583_, v_b_584_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___boxed(lean_object* v_upperBound_592_, lean_object* v_inst_593_, lean_object* v_R_594_, lean_object* v_a_595_, lean_object* v_b_596_, lean_object* v_c_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0(v_upperBound_592_, v_inst_593_, v_R_594_, v_a_595_, v_b_596_, v_c_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v_upperBound_592_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___redArg(lean_object* v_ctorName_604_, lean_object* v_as_x27_605_, lean_object* v_b_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
if (lean_obj_tag(v_as_x27_605_) == 0)
{
lean_object* v___x_612_; 
lean_dec(v_ctorName_604_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v_b_606_);
return v___x_612_;
}
else
{
lean_object* v_head_613_; lean_object* v_tail_614_; lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_662_; 
v_head_613_ = lean_ctor_get(v_as_x27_605_, 0);
v_tail_614_ = lean_ctor_get(v_as_x27_605_, 1);
v_fst_615_ = lean_ctor_get(v_b_606_, 0);
v_snd_616_ = lean_ctor_get(v_b_606_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_b_606_);
if (v_isSharedCheck_662_ == 0)
{
v___x_618_ = v_b_606_;
v_isShared_619_ = v_isSharedCheck_662_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snd_616_);
lean_inc(v_fst_615_);
lean_dec(v_b_606_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_662_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_add(v_head_613_, v___x_620_);
v___x_622_ = l_Lean_Compiler_LCNF_spillLinkIdx;
v___x_623_ = lean_nat_mul(v___x_621_, v___x_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_array_get_size(v_snd_616_);
lean_inc(v___x_623_);
v___x_625_ = l_Array_extract___redArg(v_snd_616_, v___x_623_, v___x_624_);
v___x_626_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__1));
v___x_627_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_626_, v___y_608_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref_known(v___x_627_, 1);
v___x_629_ = 1;
v___x_630_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4);
v___x_631_ = lean_array_get_size(v___x_625_);
lean_inc(v_ctorName_604_);
v___x_632_ = l_Lean_Compiler_LCNF_spillCtorInfo(v_ctorName_604_, v___x_631_);
v___x_633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_625_);
v___x_634_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_629_, v_a_628_, v___x_630_, v___x_633_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v_fvarId_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
v_fvarId_636_ = lean_ctor_get(v_a_635_, 0);
lean_inc(v_fvarId_636_);
v___x_637_ = lean_array_push(v_fst_615_, v_a_635_);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = l_Array_extract___redArg(v_snd_616_, v___x_638_, v___x_623_);
lean_dec(v_snd_616_);
v___x_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_640_, 0, v_fvarId_636_);
v___x_641_ = lean_array_push(v___x_639_, v___x_640_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v___x_641_);
lean_ctor_set(v___x_618_, 0, v___x_637_);
v___x_643_ = v___x_618_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_641_);
v___x_643_ = v_reuseFailAlloc_645_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
v_as_x27_605_ = v_tail_614_;
v_b_606_ = v___x_643_;
goto _start;
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v___x_623_);
lean_del_object(v___x_618_);
lean_dec(v_snd_616_);
lean_dec(v_fst_615_);
lean_dec(v_ctorName_604_);
v_a_646_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_634_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_634_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v___x_625_);
lean_dec(v___x_623_);
lean_del_object(v___x_618_);
lean_dec(v_snd_616_);
lean_dec(v_fst_615_);
lean_dec(v_ctorName_604_);
v_a_654_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_627_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_627_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___redArg___boxed(lean_object* v_ctorName_663_, lean_object* v_as_x27_664_, lean_object* v_b_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___redArg(v_ctorName_663_, v_as_x27_664_, v_b_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v_as_x27_664_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs(lean_object* v_ctorName_672_, lean_object* v_objArgs_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_decls_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_decls_679_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs___closed__0));
v___x_680_ = lean_array_get_size(v_objArgs_673_);
v___x_681_ = l_Lean_Compiler_LCNF_numSpillObjs(v___x_680_);
v___x_682_ = l_List_range(v___x_681_);
v___x_683_ = l_List_reverse___redArg(v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_decls_679_);
lean_ctor_set(v___x_684_, 1, v_objArgs_673_);
v___x_685_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___redArg(v_ctorName_672_, v___x_683_, v___x_684_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
lean_dec(v___x_683_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_702_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_702_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_702_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_702_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_fst_690_; lean_object* v_snd_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_701_; 
v_fst_690_ = lean_ctor_get(v_a_686_, 0);
v_snd_691_ = lean_ctor_get(v_a_686_, 1);
v_isSharedCheck_701_ = !lean_is_exclusive(v_a_686_);
if (v_isSharedCheck_701_ == 0)
{
v___x_693_ = v_a_686_;
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_snd_691_);
lean_inc(v_fst_690_);
lean_dec(v_a_686_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_fst_690_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_snd_691_);
v___x_696_ = v_reuseFailAlloc_700_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_696_);
v___x_698_ = v___x_688_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
else
{
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs___boxed(lean_object* v_ctorName_703_, lean_object* v_objArgs_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs(v_ctorName_703_, v_objArgs_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0(lean_object* v_ctorName_711_, lean_object* v_as_712_, lean_object* v_as_x27_713_, lean_object* v_b_714_, lean_object* v_a_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___redArg(v_ctorName_711_, v_as_x27_713_, v_b_714_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___boxed(lean_object* v_ctorName_722_, lean_object* v_as_723_, lean_object* v_as_x27_724_, lean_object* v_b_725_, lean_object* v_a_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0(v_ctorName_722_, v_as_723_, v_as_x27_724_, v_b_725_, v_a_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v_as_x27_724_);
lean_dec(v_as_723_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls_spec__0(lean_object* v_as_733_, size_t v_i_734_, size_t v_stop_735_, lean_object* v_b_736_){
_start:
{
uint8_t v___x_737_; 
v___x_737_ = lean_usize_dec_eq(v_i_734_, v_stop_735_);
if (v___x_737_ == 0)
{
size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_738_ = ((size_t)1ULL);
v___x_739_ = lean_usize_sub(v_i_734_, v___x_738_);
v___x_740_ = lean_array_uget_borrowed(v_as_733_, v___x_739_);
lean_inc(v___x_740_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v_b_736_);
v_i_734_ = v___x_739_;
v_b_736_ = v___x_741_;
goto _start;
}
else
{
return v_b_736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls_spec__0___boxed(lean_object* v_as_743_, lean_object* v_i_744_, lean_object* v_stop_745_, lean_object* v_b_746_){
_start:
{
size_t v_i_boxed_747_; size_t v_stop_boxed_748_; lean_object* v_res_749_; 
v_i_boxed_747_ = lean_unbox_usize(v_i_744_);
lean_dec(v_i_744_);
v_stop_boxed_748_ = lean_unbox_usize(v_stop_745_);
lean_dec(v_stop_745_);
v_res_749_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls_spec__0(v_as_743_, v_i_boxed_747_, v_stop_boxed_748_, v_b_746_);
lean_dec_ref(v_as_743_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls(lean_object* v_decls_750_, lean_object* v_code_751_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_752_ = lean_array_get_size(v_decls_750_);
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_nat_dec_lt(v___x_753_, v___x_752_);
if (v___x_754_ == 0)
{
return v_code_751_;
}
else
{
size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
v___x_755_ = lean_usize_of_nat(v___x_752_);
v___x_756_ = ((size_t)0ULL);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls_spec__0(v_decls_750_, v___x_755_, v___x_756_, v_code_751_);
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls___boxed(lean_object* v_decls_758_, lean_object* v_code_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls(v_decls_758_, v_code_759_);
lean_dec_ref(v_decls_758_);
return v_res_760_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = lean_box(0);
v___x_765_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_766_ = l_Lean_Expr_const___override(v___x_765_, v___x_764_);
return v___x_766_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2);
v___x_768_ = lean_box(1);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v___x_767_);
return v___x_769_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_box(0);
v___x_774_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5));
v___x_775_ = l_Lean_Expr_const___override(v___x_774_, v___x_773_);
return v___x_775_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_box(0);
v___x_780_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8));
v___x_781_ = l_Lean_Expr_const___override(v___x_780_, v___x_779_);
return v___x_781_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9);
v___x_783_ = lean_box(1);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v___x_782_);
return v___x_784_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__11(void){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Compiler_LCNF_instInhabitedLetDecl_default___redArg();
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(lean_object* v_base_786_, lean_object* v_spills_787_, lean_object* v_ctorInfo_788_, lean_object* v_field_789_){
_start:
{
switch(lean_obj_tag(v_field_789_))
{
case 0:
{
lean_object* v___x_790_; 
lean_dec(v_base_786_);
v___x_790_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3);
return v___x_790_;
}
case 1:
{
lean_object* v_i_791_; lean_object* v_type_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
v_i_791_ = lean_ctor_get(v_field_789_, 0);
v_type_792_ = lean_ctor_get(v_field_789_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v_field_789_);
if (v_isSharedCheck_800_ == 0)
{
v___x_794_ = v_field_789_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_type_792_);
lean_inc(v_i_791_);
lean_dec(v_field_789_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set_tag(v___x_794_, 6);
lean_ctor_set(v___x_794_, 1, v_base_786_);
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_i_791_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_base_786_);
v___x_797_ = v_reuseFailAlloc_799_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; 
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v_type_792_);
return v___x_798_;
}
}
}
case 2:
{
lean_object* v_i_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_i_801_ = lean_ctor_get(v_field_789_, 0);
lean_inc(v_i_801_);
lean_dec_ref_known(v_field_789_, 1);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v_i_801_);
lean_ctor_set(v___x_802_, 1, v_base_786_);
v___x_803_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
return v___x_804_;
}
case 3:
{
lean_object* v_offset_805_; lean_object* v_type_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_817_; 
v_offset_805_ = lean_ctor_get(v_field_789_, 1);
v_type_806_ = lean_ctor_get(v_field_789_, 2);
v_isSharedCheck_817_ = !lean_is_exclusive(v_field_789_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_field_789_, 0);
lean_dec(v_unused_818_);
v___x_808_ = v_field_789_;
v_isShared_809_ = v_isSharedCheck_817_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_type_806_);
lean_inc(v_offset_805_);
lean_dec(v_field_789_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_817_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_size_810_; lean_object* v_usize_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
v_size_810_ = lean_ctor_get(v_ctorInfo_788_, 2);
v_usize_811_ = lean_ctor_get(v_ctorInfo_788_, 3);
v___x_812_ = lean_nat_add(v_size_810_, v_usize_811_);
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 8);
lean_ctor_set(v___x_808_, 2, v_base_786_);
lean_ctor_set(v___x_808_, 0, v___x_812_);
v___x_814_ = v___x_808_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_offset_805_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_base_786_);
v___x_814_ = v_reuseFailAlloc_816_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; 
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v_type_806_);
return v___x_815_;
}
}
}
case 4:
{
lean_object* v___x_819_; 
lean_dec(v_base_786_);
v___x_819_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10);
return v___x_819_;
}
default: 
{
lean_object* v_depth_820_; lean_object* v_i_821_; lean_object* v_type_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v_fvarId_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec(v_base_786_);
v_depth_820_ = lean_ctor_get(v_field_789_, 0);
lean_inc(v_depth_820_);
v_i_821_ = lean_ctor_get(v_field_789_, 1);
lean_inc(v_i_821_);
v_type_822_ = lean_ctor_get(v_field_789_, 2);
lean_inc_ref(v_type_822_);
lean_dec_ref_known(v_field_789_, 3);
v___x_823_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__11);
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_sub(v_depth_820_, v___x_824_);
lean_dec(v_depth_820_);
v___x_826_ = lean_array_get_borrowed(v___x_823_, v_spills_787_, v___x_825_);
lean_dec(v___x_825_);
v_fvarId_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_fvarId_827_);
v___x_828_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_828_, 0, v_i_821_);
lean_ctor_set(v___x_828_, 1, v_fvarId_827_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v_type_822_);
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___boxed(lean_object* v_base_830_, lean_object* v_spills_831_, lean_object* v_ctorInfo_832_, lean_object* v_field_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_base_830_, v_spills_831_, v_ctorInfo_832_, v_field_833_);
lean_dec_ref(v_ctorInfo_832_);
lean_dec_ref(v_spills_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(lean_object* v_arg_835_, lean_object* v_a_836_){
_start:
{
uint8_t v___x_838_; uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v_subst_841_; lean_object* v___x_842_; 
v___x_838_ = 0;
v___x_839_ = 1;
v___x_840_ = lean_st_ref_get(v_a_836_);
v_subst_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc_ref(v_subst_841_);
lean_dec(v___x_840_);
v___x_842_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v___x_838_, v_subst_841_, v_arg_835_, v___x_839_);
lean_dec_ref(v_subst_841_);
if (lean_obj_tag(v___x_842_) == 1)
{
lean_object* v_fvarId_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_851_; 
v_fvarId_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_851_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_fvarId_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_fvarId_843_);
v___x_848_ = v_reuseFailAlloc_850_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; 
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v___x_842_);
v___x_852_ = lean_box(0);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg___boxed(lean_object* v_arg_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_854_, v_a_855_);
lean_dec(v_a_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(lean_object* v_arg_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_858_, v_a_859_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___boxed(lean_object* v_arg_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(v_arg_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(lean_object* v_msg_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = l_Lean_instInhabitedExpr;
v___x_876_ = lean_panic_fn_borrowed(v___x_875_, v_msg_874_);
return v___x_876_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_880_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2));
v___x_881_ = lean_unsigned_to_nat(11u);
v___x_882_ = lean_unsigned_to_nat(115u);
v___x_883_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1));
v___x_884_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_885_ = l_mkPanicMessageWithDecl(v___x_884_, v___x_883_, v___x_882_, v___x_881_, v___x_880_);
return v___x_885_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = lean_box(0);
v___x_887_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_888_ = l_Lean_mkConst(v___x_887_, v___x_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(lean_object* v_type_889_, lean_object* v_arity_890_){
_start:
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_nat_dec_eq(v_arity_890_, v___x_894_);
if (v___x_895_ == 0)
{
switch(lean_obj_tag(v_type_889_))
{
case 7:
{
lean_object* v_body_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_body_896_ = lean_ctor_get(v_type_889_, 2);
v___x_897_ = lean_unsigned_to_nat(1u);
v___x_898_ = lean_nat_sub(v_arity_890_, v___x_897_);
lean_dec(v_arity_890_);
v_type_889_ = v_body_896_;
v_arity_890_ = v___x_898_;
goto _start;
}
case 4:
{
lean_object* v_declName_900_; 
lean_dec(v_arity_890_);
v_declName_900_ = lean_ctor_get(v_type_889_, 0);
if (lean_obj_tag(v_declName_900_) == 1)
{
lean_object* v_pre_901_; 
v_pre_901_ = lean_ctor_get(v_declName_900_, 0);
if (lean_obj_tag(v_pre_901_) == 0)
{
lean_object* v_str_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v_str_902_ = lean_ctor_get(v_declName_900_, 1);
v___x_903_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0));
v___x_904_ = lean_string_dec_eq(v_str_902_, v___x_903_);
if (v___x_904_ == 0)
{
goto v___jp_891_;
}
else
{
lean_object* v___x_905_; 
v___x_905_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4);
return v___x_905_;
}
}
else
{
goto v___jp_891_;
}
}
else
{
goto v___jp_891_;
}
}
default: 
{
lean_dec(v_arity_890_);
goto v___jp_891_;
}
}
}
else
{
lean_dec(v_arity_890_);
lean_inc_ref(v_type_889_);
return v_type_889_;
}
v___jp_891_:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3);
v___x_893_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(v___x_892_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___boxed(lean_object* v_type_906_, lean_object* v_arity_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_906_, v_arity_907_);
lean_dec_ref(v_type_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object* v_type_909_, lean_object* v_arity_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_909_, v_arity_910_);
v___x_915_ = l_Lean_Compiler_LCNF_toImpureType(v___x_914_, v_a_911_, v_a_912_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType___boxed(lean_object* v_type_916_, lean_object* v_arity_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_916_, v_arity_917_, v_a_918_, v_a_919_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec_ref(v_type_916_);
return v_res_921_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_box(0);
v___x_926_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1));
v___x_927_ = l_Lean_Expr_const___override(v___x_926_, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_box(0);
v___x_932_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4));
v___x_933_ = l_Lean_Expr_const___override(v___x_932_, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_box(0);
v___x_938_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7));
v___x_939_ = l_Lean_Expr_const___override(v___x_938_, v___x_937_);
return v___x_939_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_box(0);
v___x_944_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10));
v___x_945_ = l_Lean_Expr_const___override(v___x_944_, v___x_943_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_box(0);
v___x_950_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13));
v___x_951_ = l_Lean_Expr_const___override(v___x_950_, v___x_949_);
return v___x_951_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = lean_box(0);
v___x_956_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16));
v___x_957_ = l_Lean_Expr_const___override(v___x_956_, v___x_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(lean_object* v_v_958_){
_start:
{
switch(lean_obj_tag(v_v_958_))
{
case 0:
{
lean_object* v_val_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v_val_959_ = lean_ctor_get(v_v_958_, 0);
v___x_960_ = lean_cstr_to_nat("4294967296");
v___x_961_ = lean_nat_dec_lt(v_val_959_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
v___x_962_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
return v___x_962_;
}
else
{
lean_object* v___x_963_; 
v___x_963_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
return v___x_963_;
}
}
case 1:
{
lean_object* v___x_964_; 
v___x_964_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4);
return v___x_964_;
}
case 2:
{
lean_object* v___x_965_; 
v___x_965_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
return v___x_965_;
}
case 3:
{
lean_object* v___x_966_; 
v___x_966_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11);
return v___x_966_;
}
case 4:
{
lean_object* v___x_967_; 
v___x_967_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14);
return v___x_967_;
}
case 5:
{
lean_object* v___x_968_; 
v___x_968_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17);
return v___x_968_;
}
default: 
{
lean_object* v___x_969_; 
v___x_969_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___boxed(lean_object* v_v_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_v_970_);
lean_dec_ref(v_v_970_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(lean_object* v_as_972_, size_t v_i_973_, size_t v_stop_974_, lean_object* v_b_975_){
_start:
{
lean_object* v___y_977_; uint8_t v___x_981_; 
v___x_981_ = lean_usize_dec_eq(v_i_973_, v_stop_974_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v_snd_983_; uint8_t v___x_984_; 
v___x_982_ = lean_array_uget_borrowed(v_as_972_, v_i_973_);
v_snd_983_ = lean_ctor_get(v___x_982_, 1);
v___x_984_ = lean_unbox(v_snd_983_);
if (v___x_984_ == 0)
{
v___y_977_ = v_b_975_;
goto v___jp_976_;
}
else
{
lean_object* v_fst_985_; lean_object* v___x_986_; 
v_fst_985_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_fst_985_);
v___x_986_ = lean_array_push(v_b_975_, v_fst_985_);
v___y_977_ = v___x_986_;
goto v___jp_976_;
}
}
else
{
return v_b_975_;
}
v___jp_976_:
{
size_t v___x_978_; size_t v___x_979_; 
v___x_978_ = ((size_t)1ULL);
v___x_979_ = lean_usize_add(v_i_973_, v___x_978_);
v_i_973_ = v___x_979_;
v_b_975_ = v___y_977_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4___boxed(lean_object* v_as_987_, lean_object* v_i_988_, lean_object* v_stop_989_, lean_object* v_b_990_){
_start:
{
size_t v_i_boxed_991_; size_t v_stop_boxed_992_; lean_object* v_res_993_; 
v_i_boxed_991_ = lean_unbox_usize(v_i_988_);
lean_dec(v_i_988_);
v_stop_boxed_992_ = lean_unbox_usize(v_stop_989_);
lean_dec(v_stop_989_);
v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v_as_987_, v_i_boxed_991_, v_stop_boxed_992_, v_b_990_);
lean_dec_ref(v_as_987_);
return v_res_993_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(lean_object* v_msg_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; lean_object* v_toApplicative_1003_; lean_object* v_toFunctor_1004_; lean_object* v_toSeq_1005_; lean_object* v_toSeqLeft_1006_; lean_object* v_toSeqRight_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_toApplicative_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1051_; 
v___x_1002_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_1003_ = lean_ctor_get(v___x_1002_, 0);
v_toFunctor_1004_ = lean_ctor_get(v_toApplicative_1003_, 0);
v_toSeq_1005_ = lean_ctor_get(v_toApplicative_1003_, 2);
v_toSeqLeft_1006_ = lean_ctor_get(v_toApplicative_1003_, 3);
v_toSeqRight_1007_ = lean_ctor_get(v_toApplicative_1003_, 4);
v___f_1008_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_1009_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref_n(v_toFunctor_1004_, 2);
v___f_1010_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1010_, 0, v_toFunctor_1004_);
v___f_1011_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1011_, 0, v_toFunctor_1004_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___f_1010_);
lean_ctor_set(v___x_1012_, 1, v___f_1011_);
lean_inc(v_toSeqRight_1007_);
v___f_1013_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1013_, 0, v_toSeqRight_1007_);
lean_inc(v_toSeqLeft_1006_);
v___f_1014_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1014_, 0, v_toSeqLeft_1006_);
lean_inc(v_toSeq_1005_);
v___f_1015_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1015_, 0, v_toSeq_1005_);
v___x_1016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1012_);
lean_ctor_set(v___x_1016_, 1, v___f_1008_);
lean_ctor_set(v___x_1016_, 2, v___f_1015_);
lean_ctor_set(v___x_1016_, 3, v___f_1014_);
lean_ctor_set(v___x_1016_, 4, v___f_1013_);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___f_1009_);
v___x_1018_ = l_StateRefT_x27_instMonad___redArg(v___x_1017_);
v_toApplicative_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v___x_1018_, 1);
lean_dec(v_unused_1052_);
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1051_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_toApplicative_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1051_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_toFunctor_1023_; lean_object* v_toSeq_1024_; lean_object* v_toSeqLeft_1025_; lean_object* v_toSeqRight_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1049_; 
v_toFunctor_1023_ = lean_ctor_get(v_toApplicative_1019_, 0);
v_toSeq_1024_ = lean_ctor_get(v_toApplicative_1019_, 2);
v_toSeqLeft_1025_ = lean_ctor_get(v_toApplicative_1019_, 3);
v_toSeqRight_1026_ = lean_ctor_get(v_toApplicative_1019_, 4);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_toApplicative_1019_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; 
v_unused_1050_ = lean_ctor_get(v_toApplicative_1019_, 1);
lean_dec(v_unused_1050_);
v___x_1028_ = v_toApplicative_1019_;
v_isShared_1029_ = v_isSharedCheck_1049_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_toSeqRight_1026_);
lean_inc(v_toSeqLeft_1025_);
lean_inc(v_toSeq_1024_);
lean_inc(v_toFunctor_1023_);
lean_dec(v_toApplicative_1019_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1049_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___x_1039_; 
v___f_1030_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_1031_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_1023_);
v___f_1032_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1032_, 0, v_toFunctor_1023_);
v___f_1033_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1033_, 0, v_toFunctor_1023_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___f_1032_);
lean_ctor_set(v___x_1034_, 1, v___f_1033_);
v___f_1035_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1035_, 0, v_toSeqRight_1026_);
v___f_1036_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1036_, 0, v_toSeqLeft_1025_);
v___f_1037_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1037_, 0, v_toSeq_1024_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 4, v___f_1035_);
lean_ctor_set(v___x_1028_, 3, v___f_1036_);
lean_ctor_set(v___x_1028_, 2, v___f_1037_);
lean_ctor_set(v___x_1028_, 1, v___f_1030_);
lean_ctor_set(v___x_1028_, 0, v___x_1034_);
v___x_1039_ = v___x_1028_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___f_1030_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v___f_1037_);
lean_ctor_set(v_reuseFailAlloc_1048_, 3, v___f_1036_);
lean_ctor_set(v_reuseFailAlloc_1048_, 4, v___f_1035_);
v___x_1039_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v___f_1031_);
lean_ctor_set(v___x_1021_, 0, v___x_1039_);
v___x_1041_ = v___x_1021_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___f_1031_);
v___x_1041_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_37518__overap_1045_; lean_object* v___x_1046_; 
v___x_1042_ = l_StateRefT_x27_instMonad___redArg(v___x_1041_);
v___x_1043_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0);
v___x_1044_ = l_instInhabitedOfMonad___redArg(v___x_1042_, v___x_1043_);
v___x_37518__overap_1045_ = lean_panic_fn_borrowed(v___x_1044_, v_msg_995_);
lean_dec(v___x_1044_);
lean_inc(v___y_1000_);
lean_inc_ref(v___y_999_);
lean_inc(v___y_998_);
lean_inc_ref(v___y_997_);
lean_inc(v___y_996_);
v___x_1046_ = lean_apply_6(v___x_37518__overap_1045_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, lean_box(0));
return v___x_1046_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(lean_object* v_msg_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v_msg_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_spec__10(lean_object* v_as_1061_, size_t v_i_1062_, size_t v_stop_1063_, lean_object* v_b_1064_){
_start:
{
lean_object* v___y_1066_; uint8_t v___x_1070_; 
v___x_1070_ = lean_usize_dec_eq(v_i_1062_, v_stop_1063_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1071_ = lean_array_uget_borrowed(v_as_1061_, v_i_1062_);
v___x_1072_ = l_Lean_Compiler_LCNF_CtorFieldInfo_spillDepth(v___x_1071_);
v___x_1073_ = lean_nat_dec_le(v_b_1064_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_dec(v___x_1072_);
v___y_1066_ = v_b_1064_;
goto v___jp_1065_;
}
else
{
lean_dec(v_b_1064_);
v___y_1066_ = v___x_1072_;
goto v___jp_1065_;
}
}
else
{
return v_b_1064_;
}
v___jp_1065_:
{
size_t v___x_1067_; size_t v___x_1068_; 
v___x_1067_ = ((size_t)1ULL);
v___x_1068_ = lean_usize_add(v_i_1062_, v___x_1067_);
v_i_1062_ = v___x_1068_;
v_b_1064_ = v___y_1066_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_spec__10___boxed(lean_object* v_as_1074_, lean_object* v_i_1075_, lean_object* v_stop_1076_, lean_object* v_b_1077_){
_start:
{
size_t v_i_boxed_1078_; size_t v_stop_boxed_1079_; lean_object* v_res_1080_; 
v_i_boxed_1078_ = lean_unbox_usize(v_i_1075_);
lean_dec(v_i_1075_);
v_stop_boxed_1079_ = lean_unbox_usize(v_stop_1076_);
lean_dec(v_stop_1076_);
v_res_1080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_spec__10(v_as_1074_, v_i_boxed_1078_, v_stop_boxed_1079_, v_b_1077_);
lean_dec_ref(v_as_1074_);
return v_res_1080_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(lean_object* v_upperBound_1082_, lean_object* v_params_1083_, lean_object* v___x_1084_, lean_object* v_discr_1085_, lean_object* v_a_1086_, lean_object* v_b_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_a_1091_; uint8_t v___x_1095_; 
v___x_1095_ = lean_nat_dec_lt(v_a_1086_, v_upperBound_1082_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
lean_dec(v_a_1086_);
lean_dec(v_discr_1085_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_b_1087_);
return v___x_1096_;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1097_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0);
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_array_get_borrowed(v___x_1097_, v_params_1083_, v_a_1086_);
v___x_1100_ = lean_nat_dec_eq(v_a_1086_, v___x_1084_);
if (v___x_1100_ == 0)
{
lean_object* v_fvarId_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v_subst_1104_; lean_object* v_jpParamMask_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1114_; 
v_fvarId_1101_ = lean_ctor_get(v___x_1099_, 0);
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_st_ref_take(v___y_1088_);
v_subst_1104_ = lean_ctor_get(v___x_1103_, 0);
v_jpParamMask_1105_ = lean_ctor_get(v___x_1103_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1107_ = v___x_1103_;
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_jpParamMask_1105_);
lean_inc(v_subst_1104_);
lean_dec(v___x_1103_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
lean_inc(v_fvarId_1101_);
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1104_, v_fvarId_1101_, v___x_1102_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1109_);
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_jpParamMask_1105_);
v___x_1111_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_st_ref_put(v___y_1088_, v___x_1111_);
v_a_1091_ = v___x_1098_;
goto v___jp_1090_;
}
}
}
else
{
lean_object* v_fvarId_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v_subst_1118_; lean_object* v_jpParamMask_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1128_; 
v_fvarId_1115_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_discr_1085_);
v___x_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1116_, 0, v_discr_1085_);
v___x_1117_ = lean_st_ref_take(v___y_1088_);
v_subst_1118_ = lean_ctor_get(v___x_1117_, 0);
v_jpParamMask_1119_ = lean_ctor_get(v___x_1117_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1121_ = v___x_1117_;
v_isShared_1122_ = v_isSharedCheck_1128_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_jpParamMask_1119_);
lean_inc(v_subst_1118_);
lean_dec(v___x_1117_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1128_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
lean_inc(v_fvarId_1115_);
v___x_1123_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1118_, v_fvarId_1115_, v___x_1116_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1123_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_jpParamMask_1119_);
v___x_1125_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_st_ref_put(v___y_1088_, v___x_1125_);
v_a_1091_ = v___x_1098_;
goto v___jp_1090_;
}
}
}
}
v___jp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = lean_nat_add(v_a_1086_, v___x_1092_);
lean_dec(v_a_1086_);
v_a_1086_ = v___x_1093_;
v_b_1087_ = v_a_1091_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(lean_object* v_upperBound_1129_, lean_object* v_params_1130_, lean_object* v___x_1131_, lean_object* v_discr_1132_, lean_object* v_a_1133_, lean_object* v_b_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_1129_, v_params_1130_, v___x_1131_, v_discr_1132_, v_a_1133_, v_b_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec(v___x_1131_);
lean_dec_ref(v_params_1130_);
lean_dec(v_upperBound_1129_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(size_t v_sz_1138_, size_t v_i_1139_, lean_object* v_bs_1140_){
_start:
{
uint8_t v___x_1141_; 
v___x_1141_ = lean_usize_dec_lt(v_i_1139_, v_sz_1138_);
if (v___x_1141_ == 0)
{
return v_bs_1140_;
}
else
{
lean_object* v_v_1142_; lean_object* v_type_1143_; lean_object* v___x_1144_; lean_object* v_bs_x27_1145_; uint8_t v___y_1147_; uint8_t v___x_1153_; 
v_v_1142_ = lean_array_uget_borrowed(v_bs_1140_, v_i_1139_);
v_type_1143_ = lean_ctor_get(v_v_1142_, 2);
lean_inc_ref(v_type_1143_);
v___x_1144_ = lean_unsigned_to_nat(0u);
v_bs_x27_1145_ = lean_array_uset(v_bs_1140_, v_i_1139_, v___x_1144_);
v___x_1153_ = l_Lean_Expr_isVoid(v_type_1143_);
if (v___x_1153_ == 0)
{
uint8_t v___x_1154_; 
v___x_1154_ = l_Lean_Expr_isErased(v_type_1143_);
lean_dec_ref(v_type_1143_);
if (v___x_1154_ == 0)
{
v___y_1147_ = v___x_1141_;
goto v___jp_1146_;
}
else
{
v___y_1147_ = v___x_1153_;
goto v___jp_1146_;
}
}
else
{
uint8_t v___x_1155_; 
lean_dec_ref(v_type_1143_);
v___x_1155_ = 0;
v___y_1147_ = v___x_1155_;
goto v___jp_1146_;
}
v___jp_1146_:
{
size_t v___x_1148_; size_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1148_ = ((size_t)1ULL);
v___x_1149_ = lean_usize_add(v_i_1139_, v___x_1148_);
v___x_1150_ = lean_box(v___y_1147_);
v___x_1151_ = lean_array_uset(v_bs_x27_1145_, v_i_1139_, v___x_1150_);
v_i_1139_ = v___x_1149_;
v_bs_1140_ = v___x_1151_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object* v_sz_1156_, lean_object* v_i_1157_, lean_object* v_bs_1158_){
_start:
{
size_t v_sz_boxed_1159_; size_t v_i_boxed_1160_; lean_object* v_res_1161_; 
v_sz_boxed_1159_ = lean_unbox_usize(v_sz_1156_);
lean_dec(v_sz_1156_);
v_i_boxed_1160_ = lean_unbox_usize(v_i_1157_);
lean_dec(v_i_1157_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_boxed_1159_, v_i_boxed_1160_, v_bs_1158_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(size_t v_sz_1162_, size_t v_i_1163_, lean_object* v_bs_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v___x_1167_; 
v___x_1167_ = lean_usize_dec_lt(v_i_1163_, v_sz_1162_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_bs_1164_);
return v___x_1168_;
}
else
{
lean_object* v_v_1169_; lean_object* v___x_1170_; lean_object* v_bs_x27_1171_; lean_object* v___x_1172_; 
v_v_1169_ = lean_array_uget(v_bs_1164_, v_i_1163_);
v___x_1170_ = lean_unsigned_to_nat(0u);
v_bs_x27_1171_ = lean_array_uset(v_bs_1164_, v_i_1163_, v___x_1170_);
v___x_1172_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_v_1169_, v___y_1165_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; size_t v___x_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_add(v_i_1163_, v___x_1174_);
v___x_1176_ = lean_array_uset(v_bs_x27_1171_, v_i_1163_, v_a_1173_);
v_i_1163_ = v___x_1175_;
v_bs_1164_ = v___x_1176_;
goto _start;
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_bs_x27_1171_);
v_a_1178_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1172_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1172_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(lean_object* v_sz_1186_, lean_object* v_i_1187_, lean_object* v_bs_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
size_t v_sz_boxed_1191_; size_t v_i_boxed_1192_; lean_object* v_res_1193_; 
v_sz_boxed_1191_ = lean_unbox_usize(v_sz_1186_);
lean_dec(v_sz_1186_);
v_i_boxed_1192_ = lean_unbox_usize(v_i_1187_);
lean_dec(v_i_1187_);
v_res_1193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_sz_boxed_1191_, v_i_boxed_1192_, v_bs_1188_, v___y_1189_);
lean_dec(v___y_1189_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___redArg(lean_object* v_upperBound_1194_, lean_object* v_fieldInfo_1195_, lean_object* v___x_1196_, lean_object* v_a_1197_, lean_object* v_b_1198_){
_start:
{
lean_object* v_a_1201_; uint8_t v___x_1205_; 
v___x_1205_ = lean_nat_dec_lt(v_a_1197_, v_upperBound_1194_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; 
lean_dec(v_a_1197_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_b_1198_);
return v___x_1206_;
}
else
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_array_fget_borrowed(v_fieldInfo_1195_, v_a_1197_);
switch(lean_obj_tag(v___x_1207_))
{
case 1:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_array_get_borrowed(v___x_1208_, v___x_1196_, v_a_1197_);
lean_inc(v___x_1209_);
v___x_1210_ = lean_array_push(v_b_1198_, v___x_1209_);
v_a_1201_ = v___x_1210_;
goto v___jp_1200_;
}
case 5:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = lean_array_get_borrowed(v___x_1211_, v___x_1196_, v_a_1197_);
lean_inc(v___x_1212_);
v___x_1213_ = lean_array_push(v_b_1198_, v___x_1212_);
v_a_1201_ = v___x_1213_;
goto v___jp_1200_;
}
default: 
{
v_a_1201_ = v_b_1198_;
goto v___jp_1200_;
}
}
}
v___jp_1200_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_unsigned_to_nat(1u);
v___x_1203_ = lean_nat_add(v_a_1197_, v___x_1202_);
lean_dec(v_a_1197_);
v_a_1197_ = v___x_1203_;
v_b_1198_ = v_a_1201_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___redArg___boxed(lean_object* v_upperBound_1214_, lean_object* v_fieldInfo_1215_, lean_object* v___x_1216_, lean_object* v_a_1217_, lean_object* v_b_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___redArg(v_upperBound_1214_, v_fieldInfo_1215_, v___x_1216_, v_a_1217_, v_b_1218_);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v_fieldInfo_1215_);
lean_dec(v_upperBound_1214_);
return v_res_1220_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1221_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__0);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1224_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1225_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__1);
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
lean_ctor_set(v___x_1227_, 2, v___x_1226_);
lean_ctor_set(v___x_1227_, 3, v___x_1226_);
lean_ctor_set(v___x_1227_, 4, v___x_1225_);
lean_ctor_set(v___x_1227_, 5, v___x_1225_);
lean_ctor_set(v___x_1227_, 6, v___x_1225_);
lean_ctor_set(v___x_1227_, 7, v___x_1225_);
lean_ctor_set(v___x_1227_, 8, v___x_1225_);
lean_ctor_set(v___x_1227_, 9, v___x_1225_);
lean_ctor_set(v___x_1227_, 10, v___x_1225_);
lean_ctor_set(v___x_1227_, 11, v___x_1224_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(lean_object* v_msg_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_ref_1234_; lean_object* v___x_1235_; lean_object* v_env_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_ref_1234_ = lean_ctor_get(v___y_1231_, 2);
v___x_1235_ = lean_st_ref_get(v___y_1232_);
v_env_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc_ref(v_env_1236_);
lean_dec(v___x_1235_);
v___x_1237_ = lean_st_ref_get(v___y_1230_);
v___x_1238_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1229_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1261_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1261_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1261_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v_lctx_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1259_; 
v_lctx_1243_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v___x_1237_, 1);
lean_dec(v_unused_1260_);
v___x_1245_ = v___x_1237_;
v_isShared_1246_ = v_isSharedCheck_1259_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_lctx_1243_);
lean_dec(v___x_1237_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1259_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1247_ = lean_unbox(v_a_1239_);
lean_dec(v_a_1239_);
v___x_1248_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1243_, v___x_1247_);
lean_dec_ref(v_lctx_1243_);
v___x_1249_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1231_);
v___x_1250_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__2);
v___x_1251_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1251_, 0, v_env_1236_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
lean_ctor_set(v___x_1251_, 2, v___x_1248_);
lean_ctor_set(v___x_1251_, 3, v___x_1249_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 3);
lean_ctor_set(v___x_1245_, 1, v_msg_1228_);
lean_ctor_set(v___x_1245_, 0, v___x_1251_);
v___x_1253_ = v___x_1245_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_msg_1228_);
v___x_1253_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
lean_inc(v_ref_1234_);
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_ref_1234_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set_tag(v___x_1241_, 1);
lean_ctor_set(v___x_1241_, 0, v___x_1254_);
v___x_1256_ = v___x_1241_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v___x_1237_);
lean_dec_ref(v_env_1236_);
lean_dec_ref(v_msg_1228_);
v_a_1262_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1238_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1238_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(lean_object* v_msg_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_msg_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object* v_as_1277_, size_t v_i_1278_, size_t v_stop_1279_, lean_object* v_b_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_a_1284_; uint8_t v___x_1288_; 
v___x_1288_ = lean_usize_dec_eq(v_i_1278_, v_stop_1279_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v_snd_1290_; uint8_t v___x_1291_; 
v___x_1289_ = lean_array_uget_borrowed(v_as_1277_, v_i_1278_);
v_snd_1290_ = lean_ctor_get(v___x_1289_, 1);
v___x_1291_ = lean_unbox(v_snd_1290_);
if (v___x_1291_ == 0)
{
v_a_1284_ = v_b_1280_;
goto v___jp_1283_;
}
else
{
lean_object* v_fst_1292_; lean_object* v___x_1293_; 
v_fst_1292_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_fst_1292_);
v___x_1293_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_fst_1292_, v___y_1281_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1295_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = lean_array_push(v_b_1280_, v_a_1294_);
v_a_1284_ = v___x_1295_;
goto v___jp_1283_;
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_b_1280_);
v_a_1296_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1293_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1293_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
else
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v_b_1280_);
return v___x_1304_;
}
v___jp_1283_:
{
size_t v___x_1285_; size_t v___x_1286_; 
v___x_1285_ = ((size_t)1ULL);
v___x_1286_ = lean_usize_add(v_i_1278_, v___x_1285_);
v_i_1278_ = v___x_1286_;
v_b_1280_ = v_a_1284_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object* v_as_1305_, lean_object* v_i_1306_, lean_object* v_stop_1307_, lean_object* v_b_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
size_t v_i_boxed_1311_; size_t v_stop_boxed_1312_; lean_object* v_res_1313_; 
v_i_boxed_1311_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_stop_boxed_1312_ = lean_unbox_usize(v_stop_1307_);
lean_dec(v_stop_1307_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_1305_, v_i_boxed_1311_, v_stop_boxed_1312_, v_b_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v_as_1305_);
return v_res_1313_;
}
}
static lean_object* _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17___closed__0(void){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Array_instInhabited___redArg();
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17(lean_object* v_msg_1315_){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_obj_once(&l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17___closed__0, &l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17___closed__0_once, _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17___closed__0);
v___x_1317_ = lean_panic_fn_borrowed(v___x_1316_, v_msg_1315_);
return v___x_1317_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__3(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1321_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__2));
v___x_1322_ = lean_unsigned_to_nat(11u);
v___x_1323_ = lean_unsigned_to_nat(163u);
v___x_1324_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__1));
v___x_1325_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__0));
v___x_1326_ = l_mkPanicMessageWithDecl(v___x_1325_, v___x_1324_, v___x_1323_, v___x_1322_, v___x_1321_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12(lean_object* v_a_1327_, lean_object* v_x_1328_){
_start:
{
if (lean_obj_tag(v_x_1328_) == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__3);
v___x_1330_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17(v___x_1329_);
return v___x_1330_;
}
else
{
lean_object* v_key_1331_; lean_object* v_value_1332_; lean_object* v_tail_1333_; uint8_t v___x_1334_; 
v_key_1331_ = lean_ctor_get(v_x_1328_, 0);
v_value_1332_ = lean_ctor_get(v_x_1328_, 1);
v_tail_1333_ = lean_ctor_get(v_x_1328_, 2);
v___x_1334_ = l_Lean_instBEqFVarId_beq(v_key_1331_, v_a_1327_);
if (v___x_1334_ == 0)
{
v_x_1328_ = v_tail_1333_;
goto _start;
}
else
{
lean_inc(v_value_1332_);
return v_value_1332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___boxed(lean_object* v_a_1336_, lean_object* v_x_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12(v_a_1336_, v_x_1337_);
lean_dec(v_x_1337_);
lean_dec(v_a_1336_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(lean_object* v_m_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_buckets_1341_; lean_object* v___x_1342_; uint64_t v___x_1343_; uint64_t v___x_1344_; uint64_t v___x_1345_; uint64_t v_fold_1346_; uint64_t v___x_1347_; uint64_t v___x_1348_; uint64_t v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; size_t v___x_1352_; size_t v___x_1353_; size_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_buckets_1341_ = lean_ctor_get(v_m_1339_, 1);
v___x_1342_ = lean_array_get_size(v_buckets_1341_);
v___x_1343_ = l_Lean_instHashableFVarId_hash(v_a_1340_);
v___x_1344_ = 32ULL;
v___x_1345_ = lean_uint64_shift_right(v___x_1343_, v___x_1344_);
v_fold_1346_ = lean_uint64_xor(v___x_1343_, v___x_1345_);
v___x_1347_ = 16ULL;
v___x_1348_ = lean_uint64_shift_right(v_fold_1346_, v___x_1347_);
v___x_1349_ = lean_uint64_xor(v_fold_1346_, v___x_1348_);
v___x_1350_ = lean_uint64_to_usize(v___x_1349_);
v___x_1351_ = lean_usize_of_nat(v___x_1342_);
v___x_1352_ = ((size_t)1ULL);
v___x_1353_ = lean_usize_sub(v___x_1351_, v___x_1352_);
v___x_1354_ = lean_usize_land(v___x_1350_, v___x_1353_);
v___x_1355_ = lean_array_uget_borrowed(v_buckets_1341_, v___x_1354_);
v___x_1356_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12(v_a_1340_, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(lean_object* v_m_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_m_1357_, v_a_1358_);
lean_dec(v_a_1358_);
lean_dec_ref(v_m_1357_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(size_t v_sz_1360_, size_t v_i_1361_, lean_object* v_bs_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
uint8_t v___x_1368_; 
v___x_1368_ = lean_usize_dec_lt(v_i_1361_, v_sz_1360_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v_bs_1362_);
return v___x_1369_;
}
else
{
lean_object* v_v_1370_; lean_object* v___x_1371_; lean_object* v_bs_x27_1372_; lean_object* v___x_1373_; 
v_v_1370_ = lean_array_uget(v_bs_1362_, v_i_1361_);
v___x_1371_ = lean_unsigned_to_nat(0u);
v_bs_x27_1372_ = lean_array_uset(v_bs_1362_, v_i_1361_, v___x_1371_);
v___x_1373_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_v_1370_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1373_, 1);
v___x_1375_ = ((size_t)1ULL);
v___x_1376_ = lean_usize_add(v_i_1361_, v___x_1375_);
v___x_1377_ = lean_array_uset(v_bs_x27_1372_, v_i_1361_, v_a_1374_);
v_i_1361_ = v___x_1376_;
v_bs_1362_ = v___x_1377_;
goto _start;
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec_ref(v_bs_x27_1372_);
v_a_1379_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1373_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1373_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(lean_object* v_sz_1387_, lean_object* v_i_1388_, lean_object* v_bs_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
size_t v_sz_boxed_1395_; size_t v_i_boxed_1396_; lean_object* v_res_1397_; 
v_sz_boxed_1395_ = lean_unbox_usize(v_sz_1387_);
lean_dec(v_sz_1387_);
v_i_boxed_1396_ = lean_unbox_usize(v_i_1388_);
lean_dec(v_i_1388_);
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_boxed_1395_, v_i_boxed_1396_, v_bs_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec(v___y_1390_);
return v_res_1397_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1400_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1));
v___x_1401_ = lean_unsigned_to_nat(12u);
v___x_1402_ = lean_unsigned_to_nat(148u);
v___x_1403_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1404_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1405_ = l_mkPanicMessageWithDecl(v___x_1404_, v___x_1403_, v___x_1402_, v___x_1401_, v___x_1400_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(lean_object* v_k_1406_, lean_object* v_decl_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v___x_1414_; lean_object* v_lctx_1415_; lean_object* v_nextIdx_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1436_; 
v___x_1414_ = lean_st_ref_take(v_a_1410_);
v_lctx_1415_ = lean_ctor_get(v___x_1414_, 0);
v_nextIdx_1416_ = lean_ctor_get(v___x_1414_, 1);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1418_ = v___x_1414_;
v_isShared_1419_ = v_isSharedCheck_1436_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_nextIdx_1416_);
lean_inc(v_lctx_1415_);
lean_dec(v___x_1414_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1436_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1420_ = 1;
lean_inc_ref(v_decl_1407_);
v___x_1421_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1420_, v_lctx_1415_, v_decl_1407_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1421_);
v___x_1423_ = v___x_1418_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_nextIdx_1416_);
v___x_1423_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_st_ref_put(v_a_1410_, v___x_1423_);
v___x_1425_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1406_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1434_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1434_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1434_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_decl_1407_);
lean_ctor_set(v___x_1430_, 1, v_a_1426_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1430_);
v___x_1432_ = v___x_1428_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
else
{
lean_dec_ref(v_decl_1407_);
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(lean_object* v_k_1437_, lean_object* v_fvarId_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_subst_1447_; lean_object* v_jpParamMask_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1458_; 
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_st_ref_take(v_a_1439_);
v_subst_1447_ = lean_ctor_get(v___x_1446_, 0);
v_jpParamMask_1448_ = lean_ctor_get(v___x_1446_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1450_ = v___x_1446_;
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_jpParamMask_1448_);
lean_inc(v_subst_1447_);
lean_dec(v___x_1446_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1452_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1447_, v_fvarId_1438_, v___x_1445_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1452_);
v___x_1454_ = v___x_1450_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_jpParamMask_1448_);
v___x_1454_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_st_ref_put(v_a_1439_, v___x_1454_);
v___x_1456_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1437_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(lean_object* v_decl_1460_, lean_object* v_k_1461_, lean_object* v_name_1462_, lean_object* v_numParams_1463_, lean_object* v_args_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_fvarId_1471_; lean_object* v_binderName_1472_; lean_object* v_type_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1535_; 
v_fvarId_1471_ = lean_ctor_get(v_decl_1460_, 0);
v_binderName_1472_ = lean_ctor_get(v_decl_1460_, 1);
v_type_1473_ = lean_ctor_get(v_decl_1460_, 2);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_decl_1460_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v_decl_1460_, 3);
lean_dec(v_unused_1536_);
v___x_1475_ = v_decl_1460_;
v_isShared_1476_ = v_isSharedCheck_1535_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_type_1473_);
lean_inc(v_binderName_1472_);
lean_inc(v_fvarId_1471_);
lean_dec(v_decl_1460_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1535_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1473_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1478_);
lean_dec(v_a_1478_);
v___x_1480_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1463_);
v___x_1481_ = l_Array_extract___redArg(v_args_1464_, v___x_1480_, v_numParams_1463_);
v___x_1482_ = lean_array_get_size(v_args_1464_);
v___x_1483_ = l_Array_extract___redArg(v_args_1464_, v_numParams_1463_, v___x_1482_);
v___x_1484_ = 1;
v___x_1485_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0));
lean_inc(v_binderName_1472_);
v___x_1486_ = l_Lean_Name_str___override(v_binderName_1472_, v___x_1485_);
v___x_1487_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4);
v___x_1488_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1488_, 0, v_name_1462_);
lean_ctor_set(v___x_1488_, 1, v___x_1481_);
v___x_1489_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1484_, v___x_1486_, v___x_1487_, v___x_1488_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v_fvarId_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1489_, 1);
v_fvarId_1491_ = lean_ctor_get(v_a_1490_, 0);
lean_inc(v_fvarId_1491_);
v___x_1492_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_fvarId_1491_);
lean_ctor_set(v___x_1492_, 1, v___x_1483_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 3, v___x_1492_);
lean_ctor_set(v___x_1475_, 2, v___x_1479_);
v___x_1494_ = v___x_1475_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_fvarId_1471_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_binderName_1472_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; lean_object* v_lctx_1496_; lean_object* v_nextIdx_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1517_; 
v___x_1495_ = lean_st_ref_take(v_a_1467_);
v_lctx_1496_ = lean_ctor_get(v___x_1495_, 0);
v_nextIdx_1497_ = lean_ctor_get(v___x_1495_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1499_ = v___x_1495_;
v_isShared_1500_ = v_isSharedCheck_1517_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_nextIdx_1497_);
lean_inc(v_lctx_1496_);
lean_dec(v___x_1495_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1517_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
lean_inc_ref(v___x_1494_);
v___x_1501_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1484_, v_lctx_1496_, v___x_1494_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1501_);
v___x_1503_ = v___x_1499_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_nextIdx_1497_);
v___x_1503_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = lean_st_ref_put(v_a_1467_, v___x_1503_);
v___x_1505_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1461_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1515_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1494_);
lean_ctor_set(v___x_1510_, 1, v_a_1506_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v_a_1490_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1511_);
v___x_1513_ = v___x_1508_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
else
{
lean_dec_ref(v___x_1494_);
lean_dec(v_a_1490_);
return v___x_1505_;
}
}
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v___x_1483_);
lean_dec_ref(v___x_1479_);
lean_del_object(v___x_1475_);
lean_dec(v_binderName_1472_);
lean_dec(v_fvarId_1471_);
lean_dec_ref(v_k_1461_);
v_a_1519_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1489_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1489_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_del_object(v___x_1475_);
lean_dec(v_binderName_1472_);
lean_dec(v_fvarId_1471_);
lean_dec(v_numParams_1463_);
lean_dec(v_name_1462_);
lean_dec_ref(v_k_1461_);
v_a_1527_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1477_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1477_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(lean_object* v_decl_1537_, lean_object* v_k_1538_, lean_object* v_name_1539_, lean_object* v_args_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v_fvarId_1547_; lean_object* v_binderName_1548_; lean_object* v_type_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1568_; 
v_fvarId_1547_ = lean_ctor_get(v_decl_1537_, 0);
v_binderName_1548_ = lean_ctor_get(v_decl_1537_, 1);
v_type_1549_ = lean_ctor_get(v_decl_1537_, 2);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_decl_1537_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v_decl_1537_, 3);
lean_dec(v_unused_1569_);
v___x_1551_ = v_decl_1537_;
v_isShared_1552_ = v_isSharedCheck_1568_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_type_1549_);
lean_inc(v_binderName_1548_);
lean_inc(v_fvarId_1547_);
lean_dec(v_decl_1537_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1568_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1549_, v_a_1544_, v_a_1545_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1555_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_name_1539_);
lean_ctor_set(v___x_1555_, 1, v_args_1540_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 3, v___x_1555_);
lean_ctor_set(v___x_1551_, 2, v_a_1554_);
v___x_1557_ = v___x_1551_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_fvarId_1547_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_binderName_1548_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_a_1554_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1558_; 
v___x_1558_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1538_, v___x_1557_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
return v___x_1558_;
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_del_object(v___x_1551_);
lean_dec(v_binderName_1548_);
lean_dec(v_fvarId_1547_);
lean_dec_ref(v_args_1540_);
lean_dec(v_name_1539_);
lean_dec_ref(v_k_1538_);
v_a_1560_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1553_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1553_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(lean_object* v_decl_1570_, lean_object* v_k_1571_, lean_object* v_name_1572_, lean_object* v_args_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_fvarId_1580_; lean_object* v_binderName_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1591_; 
v_fvarId_1580_ = lean_ctor_get(v_decl_1570_, 0);
v_binderName_1581_ = lean_ctor_get(v_decl_1570_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_decl_1570_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; lean_object* v_unused_1593_; 
v_unused_1592_ = lean_ctor_get(v_decl_1570_, 3);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_decl_1570_, 2);
lean_dec(v_unused_1593_);
v___x_1583_ = v_decl_1570_;
v_isShared_1584_ = v_isSharedCheck_1591_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_binderName_1581_);
lean_inc(v_fvarId_1580_);
lean_dec(v_decl_1570_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1591_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1585_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4);
v___x_1586_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_name_1572_);
lean_ctor_set(v___x_1586_, 1, v_args_1573_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 3, v___x_1586_);
lean_ctor_set(v___x_1583_, 2, v___x_1585_);
v___x_1588_ = v___x_1583_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_fvarId_1580_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_binderName_1581_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; 
v___x_1589_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1571_, v___x_1588_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
return v___x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(lean_object* v_decl_1594_, lean_object* v_k_1595_, lean_object* v_name_1596_, lean_object* v_numParams_1597_, lean_object* v_args_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_numArgs_1605_; uint8_t v___x_1606_; 
v_numArgs_1605_ = lean_array_get_size(v_args_1598_);
v___x_1606_ = lean_nat_dec_lt(v_numArgs_1605_, v_numParams_1597_);
if (v___x_1606_ == 0)
{
uint8_t v___x_1607_; 
v___x_1607_ = lean_nat_dec_eq(v_numArgs_1605_, v_numParams_1597_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; 
v___x_1608_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_1594_, v_k_1595_, v_name_1596_, v_numParams_1597_, v_args_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
lean_dec_ref(v_args_1598_);
return v___x_1608_;
}
else
{
lean_object* v___x_1609_; 
lean_dec(v_numParams_1597_);
v___x_1609_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1594_, v_k_1595_, v_name_1596_, v_args_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
return v___x_1609_;
}
}
else
{
lean_object* v___x_1610_; 
lean_dec(v_numParams_1597_);
v___x_1610_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_1594_, v_k_1595_, v_name_1596_, v_args_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
return v___x_1610_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1612_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3));
v___x_1613_ = lean_unsigned_to_nat(14u);
v___x_1614_ = lean_unsigned_to_nat(219u);
v___x_1615_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1616_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1617_ = l_mkPanicMessageWithDecl(v___x_1616_, v___x_1615_, v___x_1614_, v___x_1613_, v___x_1612_);
return v___x_1617_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
v___x_1625_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(lean_object* v_decl_1634_, lean_object* v_k_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v_fvarId_1650_; lean_object* v_binderName_1651_; lean_object* v_type_1652_; lean_object* v_value_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v_subst_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_2141_; 
v_fvarId_1650_ = lean_ctor_get(v_decl_1634_, 0);
v_binderName_1651_ = lean_ctor_get(v_decl_1634_, 1);
v_type_1652_ = lean_ctor_get(v_decl_1634_, 2);
v_value_1653_ = lean_ctor_get(v_decl_1634_, 3);
v___x_1654_ = lean_box(0);
v___x_1655_ = 0;
v___x_1656_ = 1;
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_st_ref_get(v_a_1636_);
v_subst_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_2141_ == 0)
{
lean_object* v_unused_2142_; 
v_unused_2142_ = lean_ctor_get(v___x_1658_, 1);
lean_dec(v_unused_2142_);
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_2141_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_subst_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_2141_;
goto v_resetjp_1660_;
}
v___jp_1642_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2);
v___x_1649_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1648_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
return v___x_1649_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; 
lean_inc(v_value_1653_);
v___x_1663_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v___x_1655_, v_subst_1659_, v_value_1653_, v___x_1656_);
lean_dec_ref(v_subst_1659_);
switch(lean_obj_tag(v___x_1663_))
{
case 0:
{
lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1680_; 
lean_inc(v_binderName_1651_);
lean_inc(v_fvarId_1650_);
lean_del_object(v___x_1661_);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_decl_1634_);
if (v_isSharedCheck_1680_ == 0)
{
lean_object* v_unused_1681_; lean_object* v_unused_1682_; lean_object* v_unused_1683_; lean_object* v_unused_1684_; 
v_unused_1681_ = lean_ctor_get(v_decl_1634_, 3);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_decl_1634_, 2);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v_decl_1634_, 1);
lean_dec(v_unused_1683_);
v_unused_1684_ = lean_ctor_get(v_decl_1634_, 0);
lean_dec(v_unused_1684_);
v___x_1665_ = v_decl_1634_;
v_isShared_1666_ = v_isSharedCheck_1680_;
goto v_resetjp_1664_;
}
else
{
lean_dec(v_decl_1634_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1680_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v_value_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1679_; 
v_value_1667_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1669_ = v___x_1663_;
v_isShared_1670_ = v_isSharedCheck_1679_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_value_1667_);
lean_dec(v___x_1663_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1679_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1671_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_value_1667_);
if (v_isShared_1670_ == 0)
{
v___x_1673_ = v___x_1669_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_value_1667_);
v___x_1673_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1675_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 3, v___x_1673_);
lean_ctor_set(v___x_1665_, 2, v___x_1671_);
v___x_1675_ = v___x_1665_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_fvarId_1650_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_binderName_1651_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1677_, 3, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; 
v___x_1676_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1635_, v___x_1675_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1676_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1685_; 
lean_inc(v_fvarId_1650_);
lean_del_object(v___x_1661_);
lean_dec_ref(v_decl_1634_);
v___x_1685_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1635_, v_fvarId_1650_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1685_;
}
case 2:
{
lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1805_; 
lean_inc(v_binderName_1651_);
lean_inc(v_fvarId_1650_);
lean_del_object(v___x_1661_);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_decl_1634_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; lean_object* v_unused_1807_; lean_object* v_unused_1808_; lean_object* v_unused_1809_; 
v_unused_1806_ = lean_ctor_get(v_decl_1634_, 3);
lean_dec(v_unused_1806_);
v_unused_1807_ = lean_ctor_get(v_decl_1634_, 2);
lean_dec(v_unused_1807_);
v_unused_1808_ = lean_ctor_get(v_decl_1634_, 1);
lean_dec(v_unused_1808_);
v_unused_1809_ = lean_ctor_get(v_decl_1634_, 0);
lean_dec(v_unused_1809_);
v___x_1687_ = v_decl_1634_;
v_isShared_1688_ = v_isSharedCheck_1805_;
goto v_resetjp_1686_;
}
else
{
lean_dec(v_decl_1634_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1805_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v_typeName_1689_; lean_object* v_idx_1690_; lean_object* v_struct_1691_; lean_object* v___x_1692_; 
v_typeName_1689_ = lean_ctor_get(v___x_1663_, 0);
lean_inc_n(v_typeName_1689_, 2);
v_idx_1690_ = lean_ctor_get(v___x_1663_, 1);
lean_inc(v_idx_1690_);
v_struct_1691_ = lean_ctor_get(v___x_1663_, 2);
lean_inc(v_struct_1691_);
lean_dec_ref_known(v___x_1663_, 3);
v___x_1692_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_1689_, v_a_1639_, v_a_1640_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
if (lean_obj_tag(v_a_1693_) == 1)
{
lean_object* v_val_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_typeName_1689_);
lean_del_object(v___x_1687_);
lean_dec(v_binderName_1651_);
v_val_1694_ = lean_ctor_get(v_a_1693_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_a_1693_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1696_ = v_a_1693_;
v_isShared_1697_ = v_isSharedCheck_1729_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_val_1694_);
lean_dec(v_a_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1729_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_fieldIdx_1698_; uint8_t v___x_1699_; 
v_fieldIdx_1698_ = lean_ctor_get(v_val_1694_, 2);
lean_inc(v_fieldIdx_1698_);
lean_dec(v_val_1694_);
v___x_1699_ = lean_nat_dec_eq(v_fieldIdx_1698_, v_idx_1690_);
lean_dec(v_idx_1690_);
lean_dec(v_fieldIdx_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; lean_object* v_subst_1701_; lean_object* v_jpParamMask_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1712_; 
lean_del_object(v___x_1696_);
lean_dec(v_struct_1691_);
v___x_1700_ = lean_st_ref_take(v_a_1636_);
v_subst_1701_ = lean_ctor_get(v___x_1700_, 0);
v_jpParamMask_1702_ = lean_ctor_get(v___x_1700_, 1);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1704_ = v___x_1700_;
v_isShared_1705_ = v_isSharedCheck_1712_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_jpParamMask_1702_);
lean_inc(v_subst_1701_);
lean_dec(v___x_1700_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1712_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1701_, v_fvarId_1650_, v___x_1657_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_jpParamMask_1702_);
v___x_1708_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_st_ref_put(v_a_1636_, v___x_1708_);
v___x_1710_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1710_;
}
}
}
else
{
lean_object* v___x_1714_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v_struct_1691_);
v___x_1714_ = v___x_1696_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_struct_1691_);
v___x_1714_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; lean_object* v_subst_1716_; lean_object* v_jpParamMask_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1727_; 
v___x_1715_ = lean_st_ref_take(v_a_1636_);
v_subst_1716_ = lean_ctor_get(v___x_1715_, 0);
v_jpParamMask_1717_ = lean_ctor_get(v___x_1715_, 1);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1719_ = v___x_1715_;
v_isShared_1720_ = v_isSharedCheck_1727_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_jpParamMask_1717_);
lean_inc(v_subst_1716_);
lean_dec(v___x_1715_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1727_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1721_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1716_, v_fvarId_1650_, v___x_1714_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1721_);
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_jpParamMask_1717_);
v___x_1723_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_st_ref_put(v_a_1636_, v___x_1723_);
v___x_1725_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1725_;
}
}
}
}
}
}
else
{
lean_object* v___x_1730_; lean_object* v_subst_1731_; lean_object* v___x_1732_; 
lean_dec(v_a_1693_);
v___x_1730_ = lean_st_ref_get(v_a_1636_);
v_subst_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc_ref(v_subst_1731_);
lean_dec(v___x_1730_);
v___x_1732_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1731_, v_struct_1691_, v___x_1656_);
lean_dec_ref(v_subst_1731_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_fvarId_1733_; lean_object* v___x_1734_; lean_object* v_env_1735_; uint8_t v___x_1736_; lean_object* v___x_1737_; 
v_fvarId_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_fvarId_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v___x_1734_ = lean_st_ref_get(v_a_1640_);
v_env_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc_ref(v_env_1735_);
lean_dec(v___x_1734_);
v___x_1736_ = 0;
v___x_1737_ = l_Lean_Environment_find_x3f(v_env_1735_, v_typeName_1689_, v___x_1736_);
if (lean_obj_tag(v___x_1737_) == 1)
{
lean_object* v_val_1738_; 
v_val_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_val_1738_);
lean_dec_ref_known(v___x_1737_, 1);
if (lean_obj_tag(v_val_1738_) == 5)
{
lean_object* v_val_1739_; lean_object* v_ctors_1740_; 
v_val_1739_ = lean_ctor_get(v_val_1738_, 0);
lean_inc_ref(v_val_1739_);
lean_dec_ref_known(v_val_1738_, 1);
v_ctors_1740_ = lean_ctor_get(v_val_1739_, 4);
lean_inc(v_ctors_1740_);
lean_dec_ref(v_val_1739_);
if (lean_obj_tag(v_ctors_1740_) == 1)
{
lean_object* v_tail_1741_; 
v_tail_1741_ = lean_ctor_get(v_ctors_1740_, 1);
if (lean_obj_tag(v_tail_1741_) == 0)
{
lean_object* v_head_1742_; lean_object* v___x_1743_; 
v_head_1742_ = lean_ctor_get(v_ctors_1740_, 0);
lean_inc(v_head_1742_);
lean_dec_ref_known(v_ctors_1740_, 2);
v___x_1743_ = l_Lean_Compiler_LCNF_getCtorLayout(v_head_1742_, v_a_1639_, v_a_1640_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v_ctorInfo_1745_; lean_object* v_fieldInfo_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref_known(v___x_1743_, 1);
v_ctorInfo_1745_ = lean_ctor_get(v_a_1744_, 0);
lean_inc_ref(v_ctorInfo_1745_);
v_fieldInfo_1746_ = lean_ctor_get(v_a_1744_, 1);
lean_inc_ref(v_fieldInfo_1746_);
lean_dec(v_a_1744_);
v___x_1747_ = lean_array_get(v___x_1654_, v_fieldInfo_1746_, v_idx_1690_);
lean_dec(v_idx_1690_);
lean_dec_ref(v_fieldInfo_1746_);
v___x_1748_ = l_Lean_Compiler_LCNF_CtorFieldInfo_spillDepth(v___x_1747_);
lean_inc(v_fvarId_1733_);
v___x_1749_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs(v_fvarId_1733_, v___x_1748_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
lean_dec(v___x_1748_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1751_; lean_object* v_fst_1752_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_fvarId_1733_, v_a_1750_, v_ctorInfo_1745_, v___x_1747_);
lean_dec_ref(v_ctorInfo_1745_);
v_fst_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_fst_1752_);
if (lean_obj_tag(v_fst_1752_) == 1)
{
lean_object* v___x_1753_; 
lean_dec_ref(v___x_1751_);
lean_dec(v_a_1750_);
lean_del_object(v___x_1687_);
lean_dec(v_binderName_1651_);
v___x_1753_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1635_, v_fvarId_1650_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1753_;
}
else
{
lean_object* v_snd_1754_; lean_object* v___x_1756_; 
v_snd_1754_ = lean_ctor_get(v___x_1751_, 1);
lean_inc(v_snd_1754_);
lean_dec_ref(v___x_1751_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 3, v_fst_1752_);
lean_ctor_set(v___x_1687_, 2, v_snd_1754_);
v___x_1756_ = v___x_1687_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_fvarId_1650_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_binderName_1651_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v_snd_1754_);
lean_ctor_set(v_reuseFailAlloc_1767_, 3, v_fst_1752_);
v___x_1756_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1757_; 
v___x_1757_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1635_, v___x_1756_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1766_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls(v_a_1750_, v_a_1758_);
lean_dec(v_a_1750_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1762_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
else
{
lean_dec(v_a_1750_);
return v___x_1757_;
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v___x_1747_);
lean_dec_ref(v_ctorInfo_1745_);
lean_dec(v_fvarId_1733_);
lean_del_object(v___x_1687_);
lean_dec(v_binderName_1651_);
lean_dec(v_fvarId_1650_);
lean_dec_ref(v_k_1635_);
v_a_1768_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1749_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1749_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec(v_fvarId_1733_);
lean_dec(v_idx_1690_);
lean_del_object(v___x_1687_);
lean_dec(v_binderName_1651_);
lean_dec(v_fvarId_1650_);
lean_dec_ref(v_k_1635_);
v_a_1776_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1743_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1743_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1740_, 2);
lean_dec(v_fvarId_1733_);
lean_dec(v_idx_1690_);
lean_del_object(v___x_1687_);
lean_dec(v_binderName_1651_);
lean_dec(v_fvarId_1650_);
lean_dec_ref(v_k_1635_);
v___y_1643_ = v_a_1636_;
v___y_1644_ = v_a_1637_;
v___y_1645_ = v_a_1638_;
v___y_1646_ = v_a_1639_;
v___y_1647_ = v_a_1640_;
goto v___jp_1642_;
}
}
else
{
lean_dec(v_ctors_1740_);
lean_dec(v_fvarId_1733_);
lean_dec(v_idx_1690_);
lean_del_object(v___x_1687_);
lean_dec(v_binderName_1651_);
lean_dec(v_fvarId_1650_);
lean_dec_ref(v_k_1635_);
v___y_1643_ = v_a_1636_;
v___y_1644_ = v_a_1637_;
v___y_1645_ = v_a_1638_;
v___y_1646_ = v_a_1639_;
v___y_1647_ = v_a_1640_;
goto v___jp_1642_;
}
}
else
{
lean_dec(v_val_1738_);
lean_dec(v_fvarId_1733_);
lean_dec(v_idx_1690_);
lean_del_object(v___x_1687_);
lean_dec(v_binderName_1651_);
lean_dec(v_fvarId_1650_);
lean_dec_ref(v_k_1635_);
v___y_1643_ = v_a_1636_;
v___y_1644_ = v_a_1637_;
v___y_1645_ = v_a_1638_;
v___y_1646_ = v_a_1639_;
v___y_1647_ = v_a_1640_;
goto v___jp_1642_;
}
}
else
{
lean_dec(v___x_1737_);
lean_dec(v_fvarId_1733_);
lean_dec(v_idx_1690_);
lean_del_object(v___x_1687_);
lean_dec(v_binderName_1651_);
lean_dec(v_fvarId_1650_);
lean_dec_ref(v_k_1635_);
v___y_1643_ = v_a_1636_;
v___y_1644_ = v_a_1637_;
v___y_1645_ = v_a_1638_;
v___y_1646_ = v_a_1639_;
v___y_1647_ = v_a_1640_;
goto v___jp_1642_;
}
}
else
{
lean_object* v___x_1784_; lean_object* v_subst_1785_; lean_object* v_jpParamMask_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_idx_1690_);
lean_dec(v_typeName_1689_);
lean_del_object(v___x_1687_);
lean_dec(v_binderName_1651_);
v___x_1784_ = lean_st_ref_take(v_a_1636_);
v_subst_1785_ = lean_ctor_get(v___x_1784_, 0);
v_jpParamMask_1786_ = lean_ctor_get(v___x_1784_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1788_ = v___x_1784_;
v_isShared_1789_ = v_isSharedCheck_1796_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_jpParamMask_1786_);
lean_inc(v_subst_1785_);
lean_dec(v___x_1784_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1796_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1790_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1785_, v_fvarId_1650_, v___x_1657_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1790_);
v___x_1792_ = v___x_1788_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_jpParamMask_1786_);
v___x_1792_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_st_ref_put(v_a_1636_, v___x_1792_);
v___x_1794_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1794_;
}
}
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec(v_struct_1691_);
lean_dec(v_idx_1690_);
lean_dec(v_typeName_1689_);
lean_del_object(v___x_1687_);
lean_dec(v_binderName_1651_);
lean_dec(v_fvarId_1650_);
lean_dec_ref(v_k_1635_);
v_a_1797_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1692_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1692_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
case 3:
{
lean_object* v_declName_1810_; lean_object* v_args_1811_; size_t v_sz_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v_declName_1810_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_declName_1810_);
v_args_1811_ = lean_ctor_get(v___x_1663_, 2);
lean_inc_ref_n(v_args_1811_, 2);
lean_dec_ref_known(v___x_1663_, 3);
v_sz_1812_ = lean_array_size(v_args_1811_);
v___x_1813_ = ((size_t)0ULL);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_sz_1812_, v___x_1813_, v_args_1811_, v_a_1636_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1816_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1814_, 1);
lean_inc(v_declName_1810_);
v___x_1816_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1810_, v_a_1640_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref_known(v___x_1816_, 1);
if (lean_obj_tag(v_a_1817_) == 1)
{
lean_object* v_val_1818_; lean_object* v_params_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_dec_ref(v_args_1811_);
lean_del_object(v___x_1661_);
v_val_1818_ = lean_ctor_get(v_a_1817_, 0);
lean_inc(v_val_1818_);
lean_dec_ref_known(v_a_1817_, 1);
v_params_1819_ = lean_ctor_get(v_val_1818_, 3);
lean_inc_ref(v_params_1819_);
lean_dec(v_val_1818_);
v___x_1820_ = lean_array_get_size(v_params_1819_);
lean_dec_ref(v_params_1819_);
v___x_1821_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1634_, v_k_1635_, v_declName_1810_, v___x_1820_, v_a_1815_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1821_;
}
else
{
lean_object* v___x_1822_; 
lean_dec(v_a_1817_);
lean_inc(v_declName_1810_);
v___x_1822_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1810_, v_a_1640_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 1);
if (lean_obj_tag(v_a_1823_) == 1)
{
lean_object* v_val_1824_; lean_object* v_toSignature_1825_; lean_object* v_params_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec_ref(v_args_1811_);
lean_del_object(v___x_1661_);
v_val_1824_ = lean_ctor_get(v_a_1823_, 0);
lean_inc(v_val_1824_);
lean_dec_ref_known(v_a_1823_, 1);
v_toSignature_1825_ = lean_ctor_get(v_val_1824_, 0);
lean_inc_ref(v_toSignature_1825_);
lean_dec(v_val_1824_);
v_params_1826_ = lean_ctor_get(v_toSignature_1825_, 3);
lean_inc_ref(v_params_1826_);
lean_dec_ref(v_toSignature_1825_);
v___x_1827_ = lean_array_get_size(v_params_1826_);
lean_dec_ref(v_params_1826_);
v___x_1828_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1634_, v_k_1635_, v_declName_1810_, v___x_1827_, v_a_1815_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1828_;
}
else
{
lean_object* v___x_1829_; lean_object* v_env_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; 
lean_dec(v_a_1823_);
v___x_1829_ = lean_st_ref_get(v_a_1640_);
v_env_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc_ref(v_env_1830_);
lean_dec(v___x_1829_);
v___x_1831_ = 0;
lean_inc(v_declName_1810_);
v___x_1832_ = l_Lean_Environment_find_x3f(v_env_1830_, v_declName_1810_, v___x_1831_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_dec(v_a_1815_);
lean_dec_ref(v_args_1811_);
lean_dec(v_declName_1810_);
lean_del_object(v___x_1661_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v___x_1833_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4);
v___x_1834_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1833_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1834_;
}
else
{
lean_object* v_val_1835_; 
v_val_1835_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_val_1835_);
lean_dec_ref_known(v___x_1832_, 1);
switch(lean_obj_tag(v_val_1835_))
{
case 0:
{
lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_a_1815_);
lean_dec_ref(v_args_1811_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_val_1835_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; 
v_unused_1852_ = lean_ctor_get(v_val_1835_, 0);
lean_dec(v_unused_1852_);
v___x_1837_ = v_val_1835_;
v_isShared_1838_ = v_isSharedCheck_1851_;
goto v_resetjp_1836_;
}
else
{
lean_dec(v_val_1835_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1851_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1839_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1840_ = l_Lean_Name_toString(v_declName_1810_, v___x_1656_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set_tag(v___x_1837_, 3);
lean_ctor_set(v___x_1837_, 0, v___x_1840_);
v___x_1842_ = v___x_1837_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set_tag(v___x_1661_, 5);
lean_ctor_set(v___x_1661_, 1, v___x_1842_);
lean_ctor_set(v___x_1661_, 0, v___x_1839_);
v___x_1844_ = v___x_1661_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1845_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = l_Lean_MessageData_ofFormat(v___x_1846_);
v___x_1848_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1847_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1848_;
}
}
}
}
case 2:
{
lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_a_1815_);
lean_dec_ref(v_args_1811_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_val_1835_);
if (v_isSharedCheck_1868_ == 0)
{
lean_object* v_unused_1869_; 
v_unused_1869_ = lean_ctor_get(v_val_1835_, 0);
lean_dec(v_unused_1869_);
v___x_1854_ = v_val_1835_;
v_isShared_1855_ = v_isSharedCheck_1868_;
goto v_resetjp_1853_;
}
else
{
lean_dec(v_val_1835_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1868_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1856_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1857_ = l_Lean_Name_toString(v_declName_1810_, v___x_1656_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set_tag(v___x_1854_, 3);
lean_ctor_set(v___x_1854_, 0, v___x_1857_);
v___x_1859_ = v___x_1854_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1861_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set_tag(v___x_1661_, 5);
lean_ctor_set(v___x_1661_, 1, v___x_1859_);
lean_ctor_set(v___x_1661_, 0, v___x_1856_);
v___x_1861_ = v___x_1661_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1862_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1861_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = l_Lean_MessageData_ofFormat(v___x_1863_);
v___x_1865_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1864_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1865_;
}
}
}
}
case 4:
{
lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_a_1815_);
lean_dec_ref(v_args_1811_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_val_1835_);
if (v_isSharedCheck_1885_ == 0)
{
lean_object* v_unused_1886_; 
v_unused_1886_ = lean_ctor_get(v_val_1835_, 0);
lean_dec(v_unused_1886_);
v___x_1871_ = v_val_1835_;
v_isShared_1872_ = v_isSharedCheck_1885_;
goto v_resetjp_1870_;
}
else
{
lean_dec(v_val_1835_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1885_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1873_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1874_ = l_Lean_Name_toString(v_declName_1810_, v___x_1656_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 3);
lean_ctor_set(v___x_1871_, 0, v___x_1874_);
v___x_1876_ = v___x_1871_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1878_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set_tag(v___x_1661_, 5);
lean_ctor_set(v___x_1661_, 1, v___x_1876_);
lean_ctor_set(v___x_1661_, 0, v___x_1873_);
v___x_1878_ = v___x_1661_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1879_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1878_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = l_Lean_MessageData_ofFormat(v___x_1880_);
v___x_1882_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1881_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1882_;
}
}
}
}
case 5:
{
lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_a_1815_);
lean_dec_ref(v_args_1811_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_val_1835_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v_val_1835_, 0);
lean_dec(v_unused_1903_);
v___x_1888_ = v_val_1835_;
v_isShared_1889_ = v_isSharedCheck_1902_;
goto v_resetjp_1887_;
}
else
{
lean_dec(v_val_1835_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1902_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1890_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1891_ = l_Lean_Name_toString(v_declName_1810_, v___x_1656_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 3);
lean_ctor_set(v___x_1888_, 0, v___x_1891_);
v___x_1893_ = v___x_1888_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1895_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set_tag(v___x_1661_, 5);
lean_ctor_set(v___x_1661_, 1, v___x_1893_);
lean_ctor_set(v___x_1661_, 0, v___x_1890_);
v___x_1895_ = v___x_1661_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1896_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1895_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = l_Lean_MessageData_ofFormat(v___x_1897_);
v___x_1899_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1898_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1899_;
}
}
}
}
case 6:
{
lean_object* v_val_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_2054_; 
lean_del_object(v___x_1661_);
v_val_1904_ = lean_ctor_get(v_val_1835_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_val_1835_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_1906_ = v_val_1835_;
v_isShared_1907_ = v_isSharedCheck_2054_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_val_1904_);
lean_dec(v_val_1835_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_2054_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v_induct_1908_; lean_object* v_cidx_1909_; lean_object* v_numParams_1910_; lean_object* v___x_1911_; 
v_induct_1908_ = lean_ctor_get(v_val_1904_, 1);
lean_inc_n(v_induct_1908_, 2);
v_cidx_1909_ = lean_ctor_get(v_val_1904_, 2);
lean_inc(v_cidx_1909_);
v_numParams_1910_ = lean_ctor_get(v_val_1904_, 3);
lean_inc(v_numParams_1910_);
lean_dec_ref(v_val_1904_);
v___x_1911_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_induct_1908_, v_a_1639_, v_a_1640_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
if (lean_obj_tag(v_a_1912_) == 1)
{
lean_object* v_val_1913_; lean_object* v_numParams_1914_; lean_object* v_fieldIdx_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v_subst_1919_; lean_object* v_jpParamMask_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1930_; 
lean_inc(v_fvarId_1650_);
lean_dec(v_numParams_1910_);
lean_dec(v_cidx_1909_);
lean_dec(v_induct_1908_);
lean_del_object(v___x_1906_);
lean_dec(v_a_1815_);
lean_dec(v_declName_1810_);
lean_dec_ref(v_decl_1634_);
v_val_1913_ = lean_ctor_get(v_a_1912_, 0);
lean_inc(v_val_1913_);
lean_dec_ref_known(v_a_1912_, 1);
v_numParams_1914_ = lean_ctor_get(v_val_1913_, 1);
lean_inc(v_numParams_1914_);
v_fieldIdx_1915_ = lean_ctor_get(v_val_1913_, 2);
lean_inc(v_fieldIdx_1915_);
lean_dec(v_val_1913_);
v___x_1916_ = lean_nat_add(v_numParams_1914_, v_fieldIdx_1915_);
lean_dec(v_fieldIdx_1915_);
lean_dec(v_numParams_1914_);
v___x_1917_ = lean_array_get(v___x_1657_, v_args_1811_, v___x_1916_);
lean_dec(v___x_1916_);
lean_dec_ref(v_args_1811_);
v___x_1918_ = lean_st_ref_take(v_a_1636_);
v_subst_1919_ = lean_ctor_get(v___x_1918_, 0);
v_jpParamMask_1920_ = lean_ctor_get(v___x_1918_, 1);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1922_ = v___x_1918_;
v_isShared_1923_ = v_isSharedCheck_1930_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_jpParamMask_1920_);
lean_inc(v_subst_1919_);
lean_dec(v___x_1918_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1930_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1924_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1919_, v_fvarId_1650_, v___x_1917_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_jpParamMask_1920_);
v___x_1926_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = lean_st_ref_put(v_a_1636_, v___x_1926_);
v___x_1928_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1928_;
}
}
}
else
{
lean_object* v___x_1931_; 
lean_dec(v_a_1912_);
lean_dec_ref(v_args_1811_);
v___x_1931_ = l_Lean_Compiler_LCNF_nameToImpureType(v_induct_1908_, v_a_1639_, v_a_1640_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; uint8_t v___x_1933_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_1932_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; 
lean_dec(v_a_1932_);
lean_dec(v_cidx_1909_);
lean_del_object(v___x_1906_);
lean_inc(v_declName_1810_);
v___x_1934_ = l_Lean_Compiler_LCNF_getCtorLayout(v_declName_1810_, v_a_1639_, v_a_1640_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_2013_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_2013_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_2013_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v_ctorInfo_1939_; lean_object* v_fieldInfo_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_2012_; 
v_ctorInfo_1939_ = lean_ctor_get(v_a_1935_, 0);
v_fieldInfo_1940_ = lean_ctor_get(v_a_1935_, 1);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_a_1935_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1942_ = v_a_1935_;
v_isShared_1943_ = v_isSharedCheck_2012_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_fieldInfo_1940_);
lean_inc(v_ctorInfo_1939_);
lean_dec(v_a_1935_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_2012_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1944_ = lean_array_get_size(v_a_1815_);
v___x_1945_ = l_Array_extract___redArg(v_a_1815_, v_numParams_1910_, v___x_1944_);
lean_dec(v_a_1815_);
v___x_1946_ = lean_array_get_size(v___x_1945_);
v___x_1947_ = lean_array_get_size(v_fieldInfo_1940_);
v___x_1948_ = lean_nat_dec_eq(v___x_1946_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1951_; 
lean_dec_ref(v___x_1945_);
lean_del_object(v___x_1942_);
lean_dec_ref(v_fieldInfo_1940_);
lean_dec_ref(v_ctorInfo_1939_);
lean_dec(v_declName_1810_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v___x_1949_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1949_);
v___x_1951_ = v___x_1937_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_del_object(v___x_1937_);
v___x_1953_ = lean_unsigned_to_nat(0u);
v___x_1954_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_1955_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___redArg(v___x_1947_, v_fieldInfo_1940_, v___x_1945_, v___x_1953_, v___x_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1957_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs(v_declName_1810_, v_a_1956_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v_fst_1959_; lean_object* v_snd_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1995_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v_fst_1959_ = lean_ctor_get(v_a_1958_, 0);
v_snd_1960_ = lean_ctor_get(v_a_1958_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_a_1958_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1962_ = v_a_1958_;
v_isShared_1963_ = v_isSharedCheck_1995_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_snd_1960_);
lean_inc(v_fst_1959_);
lean_dec(v_a_1958_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1995_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
uint8_t v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1964_ = 1;
v___x_1965_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_ctorInfo_1939_);
lean_inc_ref(v_ctorInfo_1939_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set_tag(v___x_1962_, 5);
lean_ctor_set(v___x_1962_, 0, v_ctorInfo_1939_);
v___x_1967_ = v___x_1962_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_ctorInfo_1939_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_snd_1960_);
v___x_1967_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v_lctx_1970_; lean_object* v_nextIdx_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1993_; 
lean_inc(v_binderName_1651_);
lean_inc(v_fvarId_1650_);
v___x_1968_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1968_, 0, v_fvarId_1650_);
lean_ctor_set(v___x_1968_, 1, v_binderName_1651_);
lean_ctor_set(v___x_1968_, 2, v___x_1965_);
lean_ctor_set(v___x_1968_, 3, v___x_1967_);
v___x_1969_ = lean_st_ref_take(v_a_1638_);
v_lctx_1970_ = lean_ctor_get(v___x_1969_, 0);
v_nextIdx_1971_ = lean_ctor_get(v___x_1969_, 1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1973_ = v___x_1969_;
v_isShared_1974_ = v_isSharedCheck_1993_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_nextIdx_1971_);
lean_inc(v_lctx_1970_);
lean_dec(v___x_1969_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1993_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
lean_inc_ref(v___x_1968_);
v___x_1975_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1964_, v_lctx_1970_, v___x_1968_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1975_);
v___x_1977_ = v___x_1973_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_nextIdx_1971_);
v___x_1977_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_st_ref_put(v_a_1638_, v___x_1977_);
v___x_1979_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_1634_, v_k_1635_, v_ctorInfo_1939_, v_fieldInfo_1940_, v___x_1945_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
lean_dec_ref(v___x_1945_);
lean_dec_ref(v_fieldInfo_1940_);
lean_dec_ref(v_ctorInfo_1939_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1991_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1991_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1991_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 1, v_a_1980_);
lean_ctor_set(v___x_1942_, 0, v___x_1968_);
v___x_1985_ = v___x_1942_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1968_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1986_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls(v_fst_1959_, v___x_1985_);
lean_dec(v_fst_1959_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1986_);
v___x_1988_ = v___x_1982_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1968_, 4);
lean_dec(v_fst_1959_);
lean_del_object(v___x_1942_);
return v___x_1979_;
}
}
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v___x_1945_);
lean_del_object(v___x_1942_);
lean_dec_ref(v_fieldInfo_1940_);
lean_dec_ref(v_ctorInfo_1939_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v_a_1996_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1957_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1957_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec_ref(v___x_1945_);
lean_del_object(v___x_1942_);
lean_dec_ref(v_fieldInfo_1940_);
lean_dec_ref(v_ctorInfo_1939_);
lean_dec(v_declName_1810_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v_a_2004_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1955_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1955_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec(v_numParams_1910_);
lean_dec(v_a_1815_);
lean_dec(v_declName_1810_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v_a_2014_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_1934_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_1934_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2033_; 
lean_inc(v_binderName_1651_);
lean_inc(v_fvarId_1650_);
lean_dec(v_numParams_1910_);
lean_dec(v_a_1815_);
lean_dec(v_declName_1810_);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_decl_1634_);
if (v_isSharedCheck_2033_ == 0)
{
lean_object* v_unused_2034_; lean_object* v_unused_2035_; lean_object* v_unused_2036_; lean_object* v_unused_2037_; 
v_unused_2034_ = lean_ctor_get(v_decl_1634_, 3);
lean_dec(v_unused_2034_);
v_unused_2035_ = lean_ctor_get(v_decl_1634_, 2);
lean_dec(v_unused_2035_);
v_unused_2036_ = lean_ctor_get(v_decl_1634_, 1);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_decl_1634_, 0);
lean_dec(v_unused_2037_);
v___x_2023_ = v_decl_1634_;
v_isShared_2024_ = v_isSharedCheck_2033_;
goto v_resetjp_2022_;
}
else
{
lean_dec(v_decl_1634_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2033_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2025_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_1932_, v_cidx_1909_);
lean_dec(v_cidx_1909_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set_tag(v___x_1906_, 0);
lean_ctor_set(v___x_1906_, 0, v___x_2025_);
v___x_2027_ = v___x_1906_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; 
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 3, v___x_2027_);
lean_ctor_set(v___x_2023_, 2, v_a_1932_);
v___x_2029_ = v___x_2023_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_fvarId_1650_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_binderName_1651_);
lean_ctor_set(v_reuseFailAlloc_2031_, 2, v_a_1932_);
lean_ctor_set(v_reuseFailAlloc_2031_, 3, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1635_, v___x_2029_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_2030_;
}
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_numParams_1910_);
lean_dec(v_cidx_1909_);
lean_del_object(v___x_1906_);
lean_dec(v_a_1815_);
lean_dec(v_declName_1810_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v_a_2038_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_1931_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_1931_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v_numParams_1910_);
lean_dec(v_cidx_1909_);
lean_dec(v_induct_1908_);
lean_del_object(v___x_1906_);
lean_dec(v_a_1815_);
lean_dec_ref(v_args_1811_);
lean_dec(v_declName_1810_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v_a_2046_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_1911_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_1911_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
case 7:
{
lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_a_1815_);
lean_dec_ref(v_args_1811_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_val_1835_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; 
v_unused_2071_ = lean_ctor_get(v_val_1835_, 0);
lean_dec(v_unused_2071_);
v___x_2056_ = v_val_1835_;
v_isShared_2057_ = v_isSharedCheck_2070_;
goto v_resetjp_2055_;
}
else
{
lean_dec(v_val_1835_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2070_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2058_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11));
v___x_2059_ = l_Lean_Name_toString(v_declName_1810_, v___x_1656_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set_tag(v___x_2056_, 3);
lean_ctor_set(v___x_2056_, 0, v___x_2059_);
v___x_2061_ = v___x_2056_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2063_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set_tag(v___x_1661_, 5);
lean_ctor_set(v___x_1661_, 1, v___x_2061_);
lean_ctor_set(v___x_1661_, 0, v___x_2058_);
v___x_2063_ = v___x_1661_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2064_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13));
v___x_2065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = l_Lean_MessageData_ofFormat(v___x_2065_);
v___x_2067_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_2066_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_2067_;
}
}
}
}
default: 
{
lean_object* v___x_2072_; 
lean_dec(v_val_1835_);
lean_dec_ref(v_args_1811_);
lean_del_object(v___x_1661_);
v___x_2072_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1634_, v_k_1635_, v_declName_1810_, v_a_1815_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_2072_;
}
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_a_1815_);
lean_dec_ref(v_args_1811_);
lean_dec(v_declName_1810_);
lean_del_object(v___x_1661_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v_a_2073_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_1822_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_1822_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_a_1815_);
lean_dec_ref(v_args_1811_);
lean_dec(v_declName_1810_);
lean_del_object(v___x_1661_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v_a_2081_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_1816_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_1816_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_args_1811_);
lean_dec(v_declName_1810_);
lean_del_object(v___x_1661_);
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_decl_1634_);
v_a_2089_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_1814_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_1814_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
default: 
{
lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2136_; 
lean_inc_ref(v_type_1652_);
lean_inc(v_binderName_1651_);
lean_inc(v_fvarId_1650_);
lean_del_object(v___x_1661_);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_decl_1634_);
if (v_isSharedCheck_2136_ == 0)
{
lean_object* v_unused_2137_; lean_object* v_unused_2138_; lean_object* v_unused_2139_; lean_object* v_unused_2140_; 
v_unused_2137_ = lean_ctor_get(v_decl_1634_, 3);
lean_dec(v_unused_2137_);
v_unused_2138_ = lean_ctor_get(v_decl_1634_, 2);
lean_dec(v_unused_2138_);
v_unused_2139_ = lean_ctor_get(v_decl_1634_, 1);
lean_dec(v_unused_2139_);
v_unused_2140_ = lean_ctor_get(v_decl_1634_, 0);
lean_dec(v_unused_2140_);
v___x_2098_ = v_decl_1634_;
v_isShared_2099_ = v_isSharedCheck_2136_;
goto v_resetjp_2097_;
}
else
{
lean_dec(v_decl_1634_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2136_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_fvarId_2100_; lean_object* v_args_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2135_; 
v_fvarId_2100_ = lean_ctor_get(v___x_1663_, 0);
v_args_2101_ = lean_ctor_get(v___x_1663_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2103_ = v___x_1663_;
v_isShared_2104_ = v_isSharedCheck_2135_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_args_2101_);
lean_inc(v_fvarId_2100_);
lean_dec(v___x_1663_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2135_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
size_t v_sz_2105_; size_t v___x_2106_; lean_object* v___x_2107_; 
v_sz_2105_ = lean_array_size(v_args_2101_);
v___x_2106_ = ((size_t)0ULL);
v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_sz_2105_, v___x_2106_, v_args_2101_, v_a_1636_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v___x_2109_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1652_, v_a_1639_, v_a_1640_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2109_, 1);
v___x_2111_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_2110_);
lean_dec(v_a_2110_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 1, v_a_2108_);
v___x_2113_ = v___x_2103_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_fvarId_2100_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 3, v___x_2113_);
lean_ctor_set(v___x_2098_, 2, v___x_2111_);
v___x_2115_ = v___x_2098_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_fvarId_1650_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_binderName_1651_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2116_; 
v___x_2116_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1635_, v___x_2115_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_2116_;
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_a_2108_);
lean_del_object(v___x_2103_);
lean_dec(v_fvarId_2100_);
lean_del_object(v___x_2098_);
lean_dec(v_binderName_1651_);
lean_dec(v_fvarId_1650_);
lean_dec_ref(v_k_1635_);
v_a_2119_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2109_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2109_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_del_object(v___x_2103_);
lean_dec(v_fvarId_2100_);
lean_del_object(v___x_2098_);
lean_dec_ref(v_type_1652_);
lean_dec(v_binderName_1651_);
lean_dec(v_fvarId_1650_);
lean_dec_ref(v_k_1635_);
v_a_2127_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2107_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2107_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2145_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1));
v___x_2146_ = lean_unsigned_to_nat(15u);
v___x_2147_ = lean_unsigned_to_nat(306u);
v___x_2148_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2149_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2150_ = l_mkPanicMessageWithDecl(v___x_2149_, v___x_2148_, v___x_2147_, v___x_2146_, v___x_2145_);
return v___x_2150_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5(void){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_2153_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2155_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6));
v___x_2156_ = lean_unsigned_to_nat(6u);
v___x_2157_ = lean_unsigned_to_nat(285u);
v___x_2158_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2159_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2160_ = l_mkPanicMessageWithDecl(v___x_2159_, v___x_2158_, v___x_2157_, v___x_2156_, v___x_2155_);
return v___x_2160_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2162_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8));
v___x_2163_ = lean_unsigned_to_nat(6u);
v___x_2164_ = lean_unsigned_to_nat(287u);
v___x_2165_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2166_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2167_ = l_mkPanicMessageWithDecl(v___x_2166_, v___x_2165_, v___x_2164_, v___x_2163_, v___x_2162_);
return v___x_2167_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2169_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10));
v___x_2170_ = lean_unsigned_to_nat(6u);
v___x_2171_ = lean_unsigned_to_nat(288u);
v___x_2172_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2173_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2174_ = l_mkPanicMessageWithDecl(v___x_2173_, v___x_2172_, v___x_2171_, v___x_2170_, v___x_2169_);
return v___x_2174_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2176_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12));
v___x_2177_ = lean_unsigned_to_nat(45u);
v___x_2178_ = lean_unsigned_to_nat(286u);
v___x_2179_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2180_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2181_ = l_mkPanicMessageWithDecl(v___x_2180_, v___x_2179_, v___x_2178_, v___x_2177_, v___x_2176_);
return v___x_2181_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2184_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1));
v___x_2185_ = lean_unsigned_to_nat(18u);
v___x_2186_ = lean_unsigned_to_nat(328u);
v___x_2187_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0));
v___x_2188_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2189_ = l_mkPanicMessageWithDecl(v___x_2188_, v___x_2187_, v___x_2186_, v___x_2185_, v___x_2184_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object* v_discr_2190_, lean_object* v_k_2191_, lean_object* v_ctorInfo_2192_, lean_object* v_spills_2193_, lean_object* v_params_2194_, lean_object* v_fields_2195_, lean_object* v_i_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = lean_array_get_size(v_params_2194_);
v___x_2212_ = lean_nat_dec_lt(v_i_2196_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; uint8_t v___x_2214_; 
lean_dec(v_discr_2190_);
v___x_2213_ = lean_array_get_size(v_fields_2195_);
v___x_2214_ = lean_nat_dec_lt(v_i_2196_, v___x_2213_);
lean_dec(v_i_2196_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; 
v___x_2215_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2191_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
return v___x_2215_;
}
else
{
lean_dec_ref(v_k_2191_);
v___y_2204_ = v_a_2197_;
v___y_2205_ = v_a_2198_;
v___y_2206_ = v_a_2199_;
v___y_2207_ = v_a_2200_;
v___y_2208_ = v_a_2201_;
goto v___jp_2203_;
}
}
else
{
lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = lean_array_get_size(v_fields_2195_);
v___x_2217_ = lean_nat_dec_lt(v_i_2196_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_dec(v_i_2196_);
lean_dec_ref(v_k_2191_);
lean_dec(v_discr_2190_);
v___y_2204_ = v_a_2197_;
v___y_2205_ = v_a_2198_;
v___y_2206_ = v_a_2199_;
v___y_2207_ = v_a_2200_;
v___y_2208_ = v_a_2201_;
goto v___jp_2203_;
}
else
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v_fst_2220_; lean_object* v_snd_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2273_; 
v___x_2218_ = lean_array_fget_borrowed(v_fields_2195_, v_i_2196_);
lean_inc(v___x_2218_);
lean_inc(v_discr_2190_);
v___x_2219_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_discr_2190_, v_spills_2193_, v_ctorInfo_2192_, v___x_2218_);
v_fst_2220_ = lean_ctor_get(v___x_2219_, 0);
v_snd_2221_ = lean_ctor_get(v___x_2219_, 1);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2223_ = v___x_2219_;
v_isShared_2224_ = v_isSharedCheck_2273_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_snd_2221_);
lean_inc(v_fst_2220_);
lean_dec(v___x_2219_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2273_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_array_fget_borrowed(v_params_2194_, v_i_2196_);
if (lean_obj_tag(v_fst_2220_) == 1)
{
lean_object* v_fvarId_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v_subst_2229_; lean_object* v_jpParamMask_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2242_; 
lean_del_object(v___x_2223_);
lean_dec(v_snd_2221_);
v_fvarId_2226_ = lean_ctor_get(v___x_2225_, 0);
v___x_2227_ = lean_box(0);
v___x_2228_ = lean_st_ref_take(v_a_2197_);
v_subst_2229_ = lean_ctor_get(v___x_2228_, 0);
v_jpParamMask_2230_ = lean_ctor_get(v___x_2228_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2232_ = v___x_2228_;
v_isShared_2233_ = v_isSharedCheck_2242_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_jpParamMask_2230_);
lean_inc(v_subst_2229_);
lean_dec(v___x_2228_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2242_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
lean_inc(v_fvarId_2226_);
v___x_2234_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_2229_, v_fvarId_2226_, v___x_2227_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_jpParamMask_2230_);
v___x_2236_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = lean_st_ref_put(v_a_2197_, v___x_2236_);
v___x_2238_ = lean_unsigned_to_nat(1u);
v___x_2239_ = lean_nat_add(v_i_2196_, v___x_2238_);
lean_dec(v_i_2196_);
v_i_2196_ = v___x_2239_;
goto _start;
}
}
}
else
{
lean_object* v_fvarId_2243_; lean_object* v_binderName_2244_; uint8_t v___x_2245_; lean_object* v_decl_2246_; lean_object* v___x_2247_; lean_object* v_lctx_2248_; lean_object* v_nextIdx_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2272_; 
v_fvarId_2243_ = lean_ctor_get(v___x_2225_, 0);
v_binderName_2244_ = lean_ctor_get(v___x_2225_, 1);
v___x_2245_ = 1;
lean_inc(v_binderName_2244_);
lean_inc(v_fvarId_2243_);
v_decl_2246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_2246_, 0, v_fvarId_2243_);
lean_ctor_set(v_decl_2246_, 1, v_binderName_2244_);
lean_ctor_set(v_decl_2246_, 2, v_snd_2221_);
lean_ctor_set(v_decl_2246_, 3, v_fst_2220_);
v___x_2247_ = lean_st_ref_take(v_a_2199_);
v_lctx_2248_ = lean_ctor_get(v___x_2247_, 0);
v_nextIdx_2249_ = lean_ctor_get(v___x_2247_, 1);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2251_ = v___x_2247_;
v_isShared_2252_ = v_isSharedCheck_2272_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_nextIdx_2249_);
lean_inc(v_lctx_2248_);
lean_dec(v___x_2247_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2272_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v___x_2255_; 
lean_inc_ref(v_decl_2246_);
v___x_2253_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2245_, v_lctx_2248_, v_decl_2246_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2253_);
v___x_2255_ = v___x_2251_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_nextIdx_2249_);
v___x_2255_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2256_ = lean_st_ref_put(v_a_2199_, v___x_2255_);
v___x_2257_ = lean_unsigned_to_nat(1u);
v___x_2258_ = lean_nat_add(v_i_2196_, v___x_2257_);
lean_dec(v_i_2196_);
v___x_2259_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2190_, v_k_2191_, v_ctorInfo_2192_, v_spills_2193_, v_params_2194_, v_fields_2195_, v___x_2258_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2270_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2262_ = v___x_2259_;
v_isShared_2263_ = v_isSharedCheck_2270_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2270_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 1, v_a_2260_);
lean_ctor_set(v___x_2223_, 0, v_decl_2246_);
v___x_2265_ = v___x_2223_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_decl_2246_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2267_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2265_);
v___x_2267_ = v___x_2262_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_dec_ref_known(v_decl_2246_, 4);
lean_del_object(v___x_2223_);
return v___x_2259_;
}
}
}
}
}
}
}
v___jp_2203_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2);
v___x_2210_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2209_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
return v___x_2210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(lean_object* v_discr_2274_, lean_object* v_alt_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
if (lean_obj_tag(v_alt_2275_) == 0)
{
lean_object* v_ctorName_2282_; lean_object* v_params_2283_; lean_object* v_code_2284_; lean_object* v___x_2285_; 
v_ctorName_2282_ = lean_ctor_get(v_alt_2275_, 0);
lean_inc(v_ctorName_2282_);
v_params_2283_ = lean_ctor_get(v_alt_2275_, 1);
lean_inc_ref(v_params_2283_);
v_code_2284_ = lean_ctor_get(v_alt_2275_, 2);
lean_inc_ref(v_code_2284_);
lean_dec_ref_known(v_alt_2275_, 3);
v___x_2285_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_2282_, v_a_2279_, v_a_2280_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v_ctorInfo_2287_; lean_object* v_fieldInfo_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2331_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v_ctorInfo_2287_ = lean_ctor_get(v_a_2286_, 0);
v_fieldInfo_2288_ = lean_ctor_get(v_a_2286_, 1);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_a_2286_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2290_ = v_a_2286_;
v_isShared_2291_ = v_isSharedCheck_2331_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_fieldInfo_2288_);
lean_inc(v_ctorInfo_2287_);
lean_dec(v_a_2286_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2331_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; lean_object* v___y_2294_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2292_ = lean_unsigned_to_nat(0u);
v___x_2326_ = lean_array_get_size(v_fieldInfo_2288_);
v___x_2327_ = lean_nat_dec_lt(v___x_2292_, v___x_2326_);
if (v___x_2327_ == 0)
{
v___y_2294_ = v___x_2292_;
goto v___jp_2293_;
}
else
{
size_t v___x_2328_; size_t v___x_2329_; lean_object* v___x_2330_; 
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = lean_usize_of_nat(v___x_2326_);
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_spec__10(v_fieldInfo_2288_, v___x_2328_, v___x_2329_, v___x_2292_);
v___y_2294_ = v___x_2330_;
goto v___jp_2293_;
}
v___jp_2293_:
{
lean_object* v___x_2295_; 
lean_inc(v_discr_2274_);
v___x_2295_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs(v_discr_2274_, v___y_2294_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
lean_dec(v___y_2294_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2297_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2295_, 1);
v___x_2297_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2274_, v_code_2284_, v_ctorInfo_2287_, v_a_2296_, v_params_2283_, v_fieldInfo_2288_, v___x_2292_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
lean_dec_ref(v_fieldInfo_2288_);
lean_dec_ref(v_params_2283_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2309_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2309_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2309_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls(v_a_2296_, v_a_2298_);
lean_dec(v_a_2296_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set_tag(v___x_2290_, 1);
lean_ctor_set(v___x_2290_, 1, v___x_2302_);
v___x_2304_ = v___x_2290_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_ctorInfo_2287_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2306_; 
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2304_);
v___x_2306_ = v___x_2300_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v_a_2296_);
lean_del_object(v___x_2290_);
lean_dec_ref(v_ctorInfo_2287_);
v_a_2310_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2297_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2297_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_del_object(v___x_2290_);
lean_dec_ref(v_fieldInfo_2288_);
lean_dec_ref(v_ctorInfo_2287_);
lean_dec_ref(v_code_2284_);
lean_dec_ref(v_params_2283_);
lean_dec(v_discr_2274_);
v_a_2318_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2295_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2295_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_code_2284_);
lean_dec_ref(v_params_2283_);
lean_dec(v_discr_2274_);
v_a_2332_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2285_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2285_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v_code_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_discr_2274_);
v_code_2340_ = lean_ctor_get(v_alt_2275_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_alt_2275_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2342_ = v_alt_2275_;
v_isShared_2343_ = v_isSharedCheck_2364_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_code_2340_);
lean_dec(v_alt_2275_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2364_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; 
v___x_2344_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_2340_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2355_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2355_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2355_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v_a_2345_);
v___x_2350_ = v___x_2342_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2352_; 
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v___x_2350_);
v___x_2352_ = v___x_2347_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_del_object(v___x_2342_);
v_a_2356_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2344_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2344_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(lean_object* v_fvarId_2365_, size_t v_sz_2366_, size_t v_i_2367_, lean_object* v_bs_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
uint8_t v___x_2375_; 
v___x_2375_ = lean_usize_dec_lt(v_i_2367_, v_sz_2366_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
lean_dec(v_fvarId_2365_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v_bs_2368_);
return v___x_2376_;
}
else
{
lean_object* v_v_2377_; lean_object* v___x_2378_; lean_object* v_bs_x27_2379_; lean_object* v___x_2380_; 
v_v_2377_ = lean_array_uget(v_bs_2368_, v_i_2367_);
v___x_2378_ = lean_unsigned_to_nat(0u);
v_bs_x27_2379_ = lean_array_uset(v_bs_2368_, v_i_2367_, v___x_2378_);
lean_inc(v_fvarId_2365_);
v___x_2380_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_fvarId_2365_, v_v_2377_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; size_t v___x_2382_; size_t v___x_2383_; lean_object* v___x_2384_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = ((size_t)1ULL);
v___x_2383_ = lean_usize_add(v_i_2367_, v___x_2382_);
v___x_2384_ = lean_array_uset(v_bs_x27_2379_, v_i_2367_, v_a_2381_);
v_i_2367_ = v___x_2383_;
v_bs_2368_ = v___x_2384_;
goto _start;
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec_ref(v_bs_x27_2379_);
lean_dec(v_fvarId_2365_);
v_a_2386_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2380_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2380_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(lean_object* v_c_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
switch(lean_obj_tag(v_c_2394_))
{
case 0:
{
lean_object* v_decl_2401_; lean_object* v_k_2402_; lean_object* v___x_2403_; 
v_decl_2401_ = lean_ctor_get(v_c_2394_, 0);
lean_inc_ref(v_decl_2401_);
v_k_2402_ = lean_ctor_get(v_c_2394_, 1);
lean_inc_ref(v_k_2402_);
lean_dec_ref_known(v_c_2394_, 2);
v___x_2403_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2401_, v_k_2402_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2403_;
}
case 1:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
lean_dec_ref_known(v_c_2394_, 2);
v___x_2404_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2);
v___x_2405_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2404_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2405_;
}
case 2:
{
lean_object* v_decl_2406_; lean_object* v_k_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2496_; 
v_decl_2406_ = lean_ctor_get(v_c_2394_, 0);
v_k_2407_ = lean_ctor_get(v_c_2394_, 1);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_c_2394_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2409_ = v_c_2394_;
v_isShared_2410_ = v_isSharedCheck_2496_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_k_2407_);
lean_inc(v_decl_2406_);
lean_dec(v_c_2394_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2496_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v_fvarId_2411_; lean_object* v_binderName_2412_; lean_object* v_params_2413_; lean_object* v_type_2414_; lean_object* v_value_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2495_; 
v_fvarId_2411_ = lean_ctor_get(v_decl_2406_, 0);
v_binderName_2412_ = lean_ctor_get(v_decl_2406_, 1);
v_params_2413_ = lean_ctor_get(v_decl_2406_, 2);
v_type_2414_ = lean_ctor_get(v_decl_2406_, 3);
v_value_2415_ = lean_ctor_get(v_decl_2406_, 4);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_decl_2406_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2417_ = v_decl_2406_;
v_isShared_2418_ = v_isSharedCheck_2495_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_value_2415_);
lean_inc(v_type_2414_);
lean_inc(v_params_2413_);
lean_inc(v_binderName_2412_);
lean_inc(v_fvarId_2411_);
lean_dec(v_decl_2406_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2495_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
size_t v_sz_2419_; size_t v___x_2420_; lean_object* v___x_2421_; 
v_sz_2419_ = lean_array_size(v_params_2413_);
v___x_2420_ = ((size_t)0ULL);
v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2419_, v___x_2420_, v_params_2413_, v_a_2395_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; size_t v_sz_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v_subst_2426_; lean_object* v_jpParamMask_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2486_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc_n(v_a_2422_, 2);
lean_dec_ref_known(v___x_2421_, 1);
v_sz_2423_ = lean_array_size(v_a_2422_);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_2423_, v___x_2420_, v_a_2422_);
v___x_2425_ = lean_st_ref_take(v_a_2395_);
v_subst_2426_ = lean_ctor_get(v___x_2425_, 0);
v_jpParamMask_2427_ = lean_ctor_get(v___x_2425_, 1);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2429_ = v___x_2425_;
v_isShared_2430_ = v_isSharedCheck_2486_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_jpParamMask_2427_);
lean_inc(v_subst_2426_);
lean_dec(v___x_2425_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2486_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
lean_inc_ref(v___x_2424_);
lean_inc(v_fvarId_2411_);
v___x_2431_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_jpParamMask_2427_, v_fvarId_2411_, v___x_2424_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 1, v___x_2431_);
v___x_2433_ = v___x_2429_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_subst_2426_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2434_; lean_object* v___y_2436_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v___x_2434_ = lean_st_ref_put(v_a_2395_, v___x_2433_);
v___x_2478_ = lean_unsigned_to_nat(0u);
v___x_2479_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3));
v___x_2480_ = l_Array_zip___redArg(v_a_2422_, v___x_2424_);
lean_dec_ref(v___x_2424_);
v___x_2481_ = lean_array_get_size(v___x_2480_);
v___x_2482_ = lean_nat_dec_lt(v___x_2478_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_dec_ref(v___x_2480_);
v___y_2436_ = v___x_2479_;
goto v___jp_2435_;
}
else
{
size_t v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_usize_of_nat(v___x_2481_);
v___x_2484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2480_, v___x_2420_, v___x_2483_, v___x_2479_);
lean_dec_ref(v___x_2480_);
v___y_2436_ = v___x_2484_;
goto v___jp_2435_;
}
v___jp_2435_:
{
lean_object* v___x_2437_; 
v___x_2437_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_value_2415_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2439_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2407_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref_known(v___x_2439_, 1);
v___x_2441_ = lean_array_get_size(v_a_2422_);
lean_dec(v_a_2422_);
v___x_2442_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2414_, v___x_2441_, v_a_2398_, v_a_2399_);
lean_dec_ref(v_type_2414_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2469_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2469_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2469_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
uint8_t v___x_2447_; lean_object* v___x_2449_; 
v___x_2447_ = 1;
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 4, v_a_2438_);
lean_ctor_set(v___x_2417_, 3, v_a_2443_);
lean_ctor_set(v___x_2417_, 2, v___y_2436_);
v___x_2449_ = v___x_2417_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_fvarId_2411_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_binderName_2412_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v___y_2436_);
lean_ctor_set(v_reuseFailAlloc_2468_, 3, v_a_2443_);
lean_ctor_set(v_reuseFailAlloc_2468_, 4, v_a_2438_);
v___x_2449_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; lean_object* v_lctx_2451_; lean_object* v_nextIdx_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2467_; 
v___x_2450_ = lean_st_ref_take(v_a_2397_);
v_lctx_2451_ = lean_ctor_get(v___x_2450_, 0);
v_nextIdx_2452_ = lean_ctor_get(v___x_2450_, 1);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2454_ = v___x_2450_;
v_isShared_2455_ = v_isSharedCheck_2467_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_nextIdx_2452_);
lean_inc(v_lctx_2451_);
lean_dec(v___x_2450_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2467_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v___x_2458_; 
lean_inc_ref(v___x_2449_);
v___x_2456_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2447_, v_lctx_2451_, v___x_2449_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2456_);
v___x_2458_ = v___x_2454_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2456_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_nextIdx_2452_);
v___x_2458_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2459_ = lean_st_ref_put(v_a_2397_, v___x_2458_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 1, v_a_2440_);
lean_ctor_set(v___x_2409_, 0, v___x_2449_);
v___x_2461_ = v___x_2409_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_a_2440_);
v___x_2461_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
lean_object* v___x_2463_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2461_);
v___x_2463_ = v___x_2445_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec(v_a_2440_);
lean_dec(v_a_2438_);
lean_dec_ref(v___y_2436_);
lean_del_object(v___x_2417_);
lean_dec(v_binderName_2412_);
lean_dec(v_fvarId_2411_);
lean_del_object(v___x_2409_);
v_a_2470_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2442_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2442_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
else
{
lean_dec(v_a_2438_);
lean_dec_ref(v___y_2436_);
lean_dec(v_a_2422_);
lean_del_object(v___x_2417_);
lean_dec_ref(v_type_2414_);
lean_dec(v_binderName_2412_);
lean_dec(v_fvarId_2411_);
lean_del_object(v___x_2409_);
return v___x_2439_;
}
}
else
{
lean_dec_ref(v___y_2436_);
lean_dec(v_a_2422_);
lean_del_object(v___x_2417_);
lean_dec_ref(v_type_2414_);
lean_dec(v_binderName_2412_);
lean_dec(v_fvarId_2411_);
lean_del_object(v___x_2409_);
lean_dec_ref(v_k_2407_);
return v___x_2437_;
}
}
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_del_object(v___x_2417_);
lean_dec_ref(v_value_2415_);
lean_dec_ref(v_type_2414_);
lean_dec(v_binderName_2412_);
lean_dec(v_fvarId_2411_);
lean_del_object(v___x_2409_);
lean_dec_ref(v_k_2407_);
v_a_2487_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2421_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2421_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2497_; lean_object* v_args_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2528_; 
v_fvarId_2497_ = lean_ctor_get(v_c_2394_, 0);
v_args_2498_ = lean_ctor_get(v_c_2394_, 1);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_c_2394_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2500_ = v_c_2394_;
v_isShared_2501_ = v_isSharedCheck_2528_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_args_2498_);
lean_inc(v_fvarId_2497_);
lean_dec(v_c_2394_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2528_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v_a_2503_; lean_object* v___x_2508_; lean_object* v_jpParamMask_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v___x_2508_ = lean_st_ref_get(v_a_2395_);
v_jpParamMask_2509_ = lean_ctor_get(v___x_2508_, 1);
lean_inc_ref(v_jpParamMask_2509_);
lean_dec(v___x_2508_);
v___x_2510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_jpParamMask_2509_, v_fvarId_2497_);
lean_dec_ref(v_jpParamMask_2509_);
v___x_2511_ = lean_unsigned_to_nat(0u);
v___x_2512_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_2513_ = l_Array_zip___redArg(v_args_2498_, v___x_2510_);
lean_dec_ref(v___x_2510_);
lean_dec_ref(v_args_2498_);
v___x_2514_ = lean_array_get_size(v___x_2513_);
v___x_2515_ = lean_nat_dec_lt(v___x_2511_, v___x_2514_);
if (v___x_2515_ == 0)
{
lean_dec_ref(v___x_2513_);
v_a_2503_ = v___x_2512_;
goto v___jp_2502_;
}
else
{
size_t v___x_2516_; size_t v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = ((size_t)0ULL);
v___x_2517_ = lean_usize_of_nat(v___x_2514_);
v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2513_, v___x_2516_, v___x_2517_, v___x_2512_, v_a_2395_);
lean_dec_ref(v___x_2513_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2518_, 1);
v_a_2503_ = v_a_2519_;
goto v___jp_2502_;
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_del_object(v___x_2500_);
lean_dec(v_fvarId_2497_);
v_a_2520_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2518_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2518_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
v___jp_2502_:
{
lean_object* v___x_2505_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 1, v_a_2503_);
v___x_2505_ = v___x_2500_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_fvarId_2497_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_a_2503_);
v___x_2505_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
}
}
}
case 4:
{
lean_object* v_cases_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2639_; 
v_cases_2529_ = lean_ctor_get(v_c_2394_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_c_2394_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2531_ = v_c_2394_;
v_isShared_2532_ = v_isSharedCheck_2639_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_cases_2529_);
lean_dec(v_c_2394_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2639_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v_typeName_2533_; lean_object* v_resultType_2534_; lean_object* v_discr_2535_; lean_object* v_alts_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2638_; 
v_typeName_2533_ = lean_ctor_get(v_cases_2529_, 0);
v_resultType_2534_ = lean_ctor_get(v_cases_2529_, 1);
v_discr_2535_ = lean_ctor_get(v_cases_2529_, 2);
v_alts_2536_ = lean_ctor_get(v_cases_2529_, 3);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_cases_2529_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2538_ = v_cases_2529_;
v_isShared_2539_ = v_isSharedCheck_2638_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_alts_2536_);
lean_inc(v_discr_2535_);
lean_inc(v_resultType_2534_);
lean_inc(v_typeName_2533_);
lean_dec(v_cases_2529_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2638_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5);
lean_inc(v_typeName_2533_);
v___x_2541_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_2533_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
if (lean_obj_tag(v_a_2542_) == 1)
{
lean_object* v_val_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
lean_del_object(v___x_2538_);
lean_dec_ref(v_resultType_2534_);
lean_dec(v_typeName_2533_);
lean_del_object(v___x_2531_);
v_val_2543_ = lean_ctor_get(v_a_2542_, 0);
lean_inc(v_val_2543_);
lean_dec_ref_known(v_a_2542_, 1);
v___x_2544_ = lean_array_get_size(v_alts_2536_);
v___x_2545_ = lean_unsigned_to_nat(1u);
v___x_2546_ = lean_nat_dec_eq(v___x_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
lean_dec(v_val_2543_);
lean_dec_ref(v_alts_2536_);
lean_dec(v_discr_2535_);
v___x_2547_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7);
v___x_2548_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2547_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2548_;
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = lean_array_get(v___x_2540_, v_alts_2536_, v___x_2549_);
lean_dec_ref(v_alts_2536_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_ctorName_2551_; lean_object* v_params_2552_; lean_object* v_code_2553_; lean_object* v_ctorName_2554_; lean_object* v_fieldIdx_2555_; uint8_t v___x_2556_; 
v_ctorName_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_ctorName_2551_);
v_params_2552_ = lean_ctor_get(v___x_2550_, 1);
lean_inc_ref(v_params_2552_);
v_code_2553_ = lean_ctor_get(v___x_2550_, 2);
lean_inc_ref(v_code_2553_);
lean_dec_ref_known(v___x_2550_, 3);
v_ctorName_2554_ = lean_ctor_get(v_val_2543_, 0);
lean_inc(v_ctorName_2554_);
v_fieldIdx_2555_ = lean_ctor_get(v_val_2543_, 2);
lean_inc(v_fieldIdx_2555_);
lean_dec(v_val_2543_);
v___x_2556_ = lean_name_eq(v_ctorName_2551_, v_ctorName_2554_);
lean_dec(v_ctorName_2554_);
lean_dec(v_ctorName_2551_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
lean_dec(v_fieldIdx_2555_);
lean_dec_ref(v_code_2553_);
lean_dec_ref(v_params_2552_);
lean_dec(v_discr_2535_);
v___x_2557_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9);
v___x_2558_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2557_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2558_;
}
else
{
lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2559_ = lean_array_get_size(v_params_2552_);
v___x_2560_ = lean_nat_dec_lt(v_fieldIdx_2555_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
lean_dec(v_fieldIdx_2555_);
lean_dec_ref(v_code_2553_);
lean_dec_ref(v_params_2552_);
lean_dec(v_discr_2535_);
v___x_2561_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11);
v___x_2562_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2561_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2562_;
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_box(0);
v___x_2564_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v___x_2559_, v_params_2552_, v_fieldIdx_2555_, v_discr_2535_, v___x_2549_, v___x_2563_, v_a_2395_);
lean_dec(v_fieldIdx_2555_);
lean_dec_ref(v_params_2552_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_dec_ref_known(v___x_2564_, 1);
v_c_2394_ = v_code_2553_;
goto _start;
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec_ref(v_code_2553_);
v_a_2566_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2564_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2564_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_dec(v___x_2550_);
lean_dec(v_val_2543_);
lean_dec(v_discr_2535_);
v___x_2574_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13);
v___x_2575_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2574_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2575_;
}
}
}
else
{
uint8_t v___x_2576_; lean_object* v___x_2577_; lean_object* v_subst_2578_; lean_object* v___x_2579_; 
lean_dec(v_a_2542_);
v___x_2576_ = 1;
v___x_2577_ = lean_st_ref_get(v_a_2395_);
v_subst_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc_ref(v_subst_2578_);
lean_dec(v___x_2577_);
v___x_2579_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2578_, v_discr_2535_, v___x_2576_);
lean_dec_ref(v_subst_2578_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_fvarId_2580_; lean_object* v___x_2581_; 
v_fvarId_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_fvarId_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2581_ = l_Lean_Compiler_LCNF_toImpureType(v_resultType_2534_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; size_t v_sz_2583_; size_t v___x_2584_; lean_object* v___x_2585_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v_sz_2583_ = lean_array_size(v_alts_2536_);
v___x_2584_ = ((size_t)0ULL);
lean_inc(v_fvarId_2580_);
v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2580_, v_sz_2583_, v___x_2584_, v_alts_2536_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2587_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v___x_2585_, 1);
v___x_2587_ = l_Lean_Compiler_LCNF_nameToImpureType(v_typeName_2533_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2603_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2603_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2603_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2592_ = l_Lean_Expr_getAppFn(v_a_2588_);
lean_dec(v_a_2588_);
v___x_2593_ = l_Lean_Expr_constName_x21(v___x_2592_);
lean_dec_ref(v___x_2592_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 3, v_a_2586_);
lean_ctor_set(v___x_2538_, 2, v_fvarId_2580_);
lean_ctor_set(v___x_2538_, 1, v_a_2582_);
lean_ctor_set(v___x_2538_, 0, v___x_2593_);
v___x_2595_ = v___x_2538_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_a_2582_);
lean_ctor_set(v_reuseFailAlloc_2602_, 2, v_fvarId_2580_);
lean_ctor_set(v_reuseFailAlloc_2602_, 3, v_a_2586_);
v___x_2595_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2597_; 
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 0, v___x_2595_);
v___x_2597_ = v___x_2531_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2599_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2597_);
v___x_2599_ = v___x_2590_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v_a_2586_);
lean_dec(v_a_2582_);
lean_dec(v_fvarId_2580_);
lean_del_object(v___x_2538_);
lean_del_object(v___x_2531_);
v_a_2604_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2587_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2587_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec(v_a_2582_);
lean_dec(v_fvarId_2580_);
lean_del_object(v___x_2538_);
lean_dec(v_typeName_2533_);
lean_del_object(v___x_2531_);
v_a_2612_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2585_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2585_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v_fvarId_2580_);
lean_del_object(v___x_2538_);
lean_dec_ref(v_alts_2536_);
lean_dec(v_typeName_2533_);
lean_del_object(v___x_2531_);
v_a_2620_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2581_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2581_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
else
{
uint8_t v___x_2628_; lean_object* v___x_2629_; 
lean_del_object(v___x_2538_);
lean_dec_ref(v_alts_2536_);
lean_dec_ref(v_resultType_2534_);
lean_dec(v_typeName_2533_);
lean_del_object(v___x_2531_);
v___x_2628_ = 1;
v___x_2629_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2628_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2629_;
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_del_object(v___x_2538_);
lean_dec_ref(v_alts_2536_);
lean_dec(v_discr_2535_);
lean_dec_ref(v_resultType_2534_);
lean_dec(v_typeName_2533_);
lean_del_object(v___x_2531_);
v_a_2630_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2541_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2541_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2661_; 
v_fvarId_2640_ = lean_ctor_get(v_c_2394_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_c_2394_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2642_ = v_c_2394_;
v_isShared_2643_ = v_isSharedCheck_2661_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_fvarId_2640_);
lean_dec(v_c_2394_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2661_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
uint8_t v___x_2644_; lean_object* v___x_2645_; lean_object* v_subst_2646_; lean_object* v___x_2647_; 
v___x_2644_ = 1;
v___x_2645_ = lean_st_ref_get(v_a_2395_);
v_subst_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc_ref(v_subst_2646_);
lean_dec(v___x_2645_);
v___x_2647_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2646_, v_fvarId_2640_, v___x_2644_);
lean_dec_ref(v_subst_2646_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_fvarId_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2658_; 
v_fvarId_2648_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2650_ = v___x_2647_;
v_isShared_2651_ = v_isSharedCheck_2658_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_fvarId_2648_);
lean_dec(v___x_2647_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2658_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v_fvarId_2648_);
v___x_2653_ = v___x_2642_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_fvarId_2648_);
v___x_2653_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2655_; 
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v___x_2653_);
v___x_2655_ = v___x_2650_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
else
{
uint8_t v___x_2659_; lean_object* v___x_2660_; 
lean_del_object(v___x_2642_);
v___x_2659_ = 1;
v___x_2660_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2659_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2660_;
}
}
}
default: 
{
lean_object* v_type_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2686_; 
v_type_2662_ = lean_ctor_get(v_c_2394_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_c_2394_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2664_ = v_c_2394_;
v_isShared_2665_ = v_isSharedCheck_2686_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_type_2662_);
lean_dec(v_c_2394_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2686_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_Compiler_LCNF_toImpureType(v_type_2662_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2677_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2677_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2677_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v_a_2667_);
v___x_2672_ = v___x_2664_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2674_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2672_);
v___x_2674_ = v___x_2669_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_del_object(v___x_2664_);
v_a_2678_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2666_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2666_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(lean_object* v_decl_2687_, lean_object* v_k_2688_, lean_object* v_ctorInfo_2689_, lean_object* v_fields_2690_, lean_object* v_irArgs_2691_, lean_object* v_i_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2699_ = lean_array_get_size(v_irArgs_2691_);
v___x_2700_ = lean_nat_dec_lt(v_i_2692_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; 
lean_dec(v_i_2692_);
lean_dec_ref(v_decl_2687_);
v___x_2701_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2688_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
return v___x_2701_;
}
else
{
lean_object* v___x_2702_; 
v___x_2702_ = lean_array_fget_borrowed(v_irArgs_2691_, v_i_2692_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = lean_unsigned_to_nat(1u);
v___x_2704_ = lean_nat_add(v_i_2692_, v___x_2703_);
lean_dec(v_i_2692_);
v_i_2692_ = v___x_2704_;
goto _start;
}
else
{
lean_object* v_fvarId_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_fvarId_2706_ = lean_ctor_get(v___x_2702_, 0);
v___x_2707_ = lean_box(0);
v___x_2708_ = lean_array_get_borrowed(v___x_2707_, v_fields_2690_, v_i_2692_);
switch(lean_obj_tag(v___x_2708_))
{
case 2:
{
lean_object* v_i_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v_i_2709_ = lean_ctor_get(v___x_2708_, 0);
v___x_2710_ = lean_unsigned_to_nat(1u);
v___x_2711_ = lean_nat_add(v_i_2692_, v___x_2710_);
lean_dec(v_i_2692_);
lean_inc_ref(v_decl_2687_);
v___x_2712_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2687_, v_k_2688_, v_ctorInfo_2689_, v_fields_2690_, v_irArgs_2691_, v___x_2711_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2731_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2731_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2731_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v_fvarId_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2727_; 
v_fvarId_2717_ = lean_ctor_get(v_decl_2687_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_decl_2687_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; lean_object* v_unused_2729_; lean_object* v_unused_2730_; 
v_unused_2728_ = lean_ctor_get(v_decl_2687_, 3);
lean_dec(v_unused_2728_);
v_unused_2729_ = lean_ctor_get(v_decl_2687_, 2);
lean_dec(v_unused_2729_);
v_unused_2730_ = lean_ctor_get(v_decl_2687_, 1);
lean_dec(v_unused_2730_);
v___x_2719_ = v_decl_2687_;
v_isShared_2720_ = v_isSharedCheck_2727_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_fvarId_2717_);
lean_dec(v_decl_2687_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2727_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
lean_inc(v_fvarId_2706_);
lean_inc(v_i_2709_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set_tag(v___x_2719_, 8);
lean_ctor_set(v___x_2719_, 3, v_a_2713_);
lean_ctor_set(v___x_2719_, 2, v_fvarId_2706_);
lean_ctor_set(v___x_2719_, 1, v_i_2709_);
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_fvarId_2717_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_i_2709_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_fvarId_2706_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v_a_2713_);
v___x_2722_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2724_; 
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2722_);
v___x_2724_ = v___x_2715_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_2687_);
return v___x_2712_;
}
}
case 3:
{
lean_object* v_offset_2732_; lean_object* v_type_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_offset_2732_ = lean_ctor_get(v___x_2708_, 1);
v_type_2733_ = lean_ctor_get(v___x_2708_, 2);
v___x_2734_ = lean_unsigned_to_nat(1u);
v___x_2735_ = lean_nat_add(v_i_2692_, v___x_2734_);
lean_dec(v_i_2692_);
lean_inc_ref(v_decl_2687_);
v___x_2736_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2687_, v_k_2688_, v_ctorInfo_2689_, v_fields_2690_, v_irArgs_2691_, v___x_2735_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2749_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2739_ = v___x_2736_;
v_isShared_2740_ = v_isSharedCheck_2749_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2749_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v_fvarId_2741_; lean_object* v_size_2742_; lean_object* v_usize_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
v_fvarId_2741_ = lean_ctor_get(v_decl_2687_, 0);
lean_inc(v_fvarId_2741_);
lean_dec_ref(v_decl_2687_);
v_size_2742_ = lean_ctor_get(v_ctorInfo_2689_, 2);
v_usize_2743_ = lean_ctor_get(v_ctorInfo_2689_, 3);
v___x_2744_ = lean_nat_add(v_size_2742_, v_usize_2743_);
lean_inc_ref(v_type_2733_);
lean_inc(v_fvarId_2706_);
lean_inc(v_offset_2732_);
v___x_2745_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_2745_, 0, v_fvarId_2741_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
lean_ctor_set(v___x_2745_, 2, v_offset_2732_);
lean_ctor_set(v___x_2745_, 3, v_fvarId_2706_);
lean_ctor_set(v___x_2745_, 4, v_type_2733_);
lean_ctor_set(v___x_2745_, 5, v_a_2737_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 0, v___x_2745_);
v___x_2747_ = v___x_2739_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
else
{
lean_dec_ref(v_decl_2687_);
return v___x_2736_;
}
}
default: 
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = lean_unsigned_to_nat(1u);
v___x_2751_ = lean_nat_add(v_i_2692_, v___x_2750_);
lean_dec(v_i_2692_);
v_i_2692_ = v___x_2751_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(lean_object* v_decl_2753_, lean_object* v_k_2754_, lean_object* v_ctorInfo_2755_, lean_object* v_fields_2756_, lean_object* v_irArgs_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = lean_unsigned_to_nat(0u);
v___x_2765_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2753_, v_k_2754_, v_ctorInfo_2755_, v_fields_2756_, v_irArgs_2757_, v___x_2764_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(lean_object* v_decl_2766_, lean_object* v_k_2767_, lean_object* v_ctorInfo_2768_, lean_object* v_fields_2769_, lean_object* v_irArgs_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_2766_, v_k_2767_, v_ctorInfo_2768_, v_fields_2769_, v_irArgs_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_irArgs_2770_);
lean_dec_ref(v_fields_2769_);
lean_dec_ref(v_ctorInfo_2768_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(lean_object* v_decl_2778_, lean_object* v_k_2779_, lean_object* v_name_2780_, lean_object* v_args_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_2778_, v_k_2779_, v_name_2780_, v_args_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
lean_dec(v_a_2786_);
lean_dec_ref(v_a_2785_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(lean_object* v_decl_2789_, lean_object* v_k_2790_, lean_object* v_name_2791_, lean_object* v_args_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_2789_, v_k_2790_, v_name_2791_, v_args_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
lean_dec(v_a_2793_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object* v_k_2800_, lean_object* v_fvarId_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_2800_, v_fvarId_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object* v_decl_2809_, lean_object* v_k_2810_, lean_object* v_name_2811_, lean_object* v_numParams_2812_, lean_object* v_args_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_2809_, v_k_2810_, v_name_2811_, v_numParams_2812_, v_args_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object* v_fvarId_2821_, lean_object* v_sz_2822_, lean_object* v_i_2823_, lean_object* v_bs_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
size_t v_sz_boxed_2831_; size_t v_i_boxed_2832_; lean_object* v_res_2833_; 
v_sz_boxed_2831_ = lean_unbox_usize(v_sz_2822_);
lean_dec(v_sz_2822_);
v_i_boxed_2832_ = lean_unbox_usize(v_i_2823_);
lean_dec(v_i_2823_);
v_res_2833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2821_, v_sz_boxed_2831_, v_i_boxed_2832_, v_bs_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object* v_k_2834_, lean_object* v_decl_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_2834_, v_decl_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
lean_dec(v_a_2838_);
lean_dec_ref(v_a_2837_);
lean_dec(v_a_2836_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object* v_discr_2843_, lean_object* v_alt_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_discr_2843_, v_alt_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* v_decl_2852_, lean_object* v_k_2853_, lean_object* v_ctorInfo_2854_, lean_object* v_fields_2855_, lean_object* v_irArgs_2856_, lean_object* v_i_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2852_, v_k_2853_, v_ctorInfo_2854_, v_fields_2855_, v_irArgs_2856_, v_i_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
lean_dec(v_a_2858_);
lean_dec_ref(v_irArgs_2856_);
lean_dec_ref(v_fields_2855_);
lean_dec_ref(v_ctorInfo_2854_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object* v_decl_2865_, lean_object* v_k_2866_, lean_object* v_name_2867_, lean_object* v_numParams_2868_, lean_object* v_args_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_2865_, v_k_2866_, v_name_2867_, v_numParams_2868_, v_args_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
lean_dec(v_a_2870_);
lean_dec_ref(v_args_2869_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(lean_object* v_discr_2877_, lean_object* v_k_2878_, lean_object* v_ctorInfo_2879_, lean_object* v_spills_2880_, lean_object* v_params_2881_, lean_object* v_fields_2882_, lean_object* v_i_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2877_, v_k_2878_, v_ctorInfo_2879_, v_spills_2880_, v_params_2881_, v_fields_2882_, v_i_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec(v_a_2884_);
lean_dec_ref(v_fields_2882_);
lean_dec_ref(v_params_2881_);
lean_dec_ref(v_spills_2880_);
lean_dec_ref(v_ctorInfo_2879_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(lean_object* v_c_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_c_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(lean_object* v_decl_2899_, lean_object* v_k_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2899_, v_k_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
lean_dec(v_a_2901_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(lean_object* v_00_u03b1_2908_, lean_object* v_msg_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_msg_2909_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(lean_object* v_00_u03b1_2917_, lean_object* v_msg_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(v_00_u03b1_2917_, v_msg_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(size_t v_sz_2926_, size_t v_i_2927_, lean_object* v_bs_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2926_, v_i_2927_, v_bs_2928_, v___y_2929_, v___y_2931_, v___y_2932_, v___y_2933_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(lean_object* v_sz_2936_, lean_object* v_i_2937_, lean_object* v_bs_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
size_t v_sz_boxed_2945_; size_t v_i_boxed_2946_; lean_object* v_res_2947_; 
v_sz_boxed_2945_ = lean_unbox_usize(v_sz_2936_);
lean_dec(v_sz_2936_);
v_i_boxed_2946_ = lean_unbox_usize(v_i_2937_);
lean_dec(v_i_2937_);
v_res_2947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(v_sz_boxed_2945_, v_i_boxed_2946_, v_bs_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(lean_object* v_as_2948_, size_t v_i_2949_, size_t v_stop_2950_, lean_object* v_b_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_2948_, v_i_2949_, v_stop_2950_, v_b_2951_, v___y_2952_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(lean_object* v_as_2959_, lean_object* v_i_2960_, lean_object* v_stop_2961_, lean_object* v_b_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
size_t v_i_boxed_2969_; size_t v_stop_boxed_2970_; lean_object* v_res_2971_; 
v_i_boxed_2969_ = lean_unbox_usize(v_i_2960_);
lean_dec(v_i_2960_);
v_stop_boxed_2970_ = lean_unbox_usize(v_stop_2961_);
lean_dec(v_stop_2961_);
v_res_2971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(v_as_2959_, v_i_boxed_2969_, v_stop_boxed_2970_, v_b_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v_as_2959_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(lean_object* v_upperBound_2972_, lean_object* v_params_2973_, lean_object* v___x_2974_, lean_object* v_discr_2975_, lean_object* v_inst_2976_, lean_object* v_R_2977_, lean_object* v_a_2978_, lean_object* v_b_2979_, lean_object* v_c_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_2972_, v_params_2973_, v___x_2974_, v_discr_2975_, v_a_2978_, v_b_2979_, v___y_2981_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(lean_object* v_upperBound_2988_, lean_object* v_params_2989_, lean_object* v___x_2990_, lean_object* v_discr_2991_, lean_object* v_inst_2992_, lean_object* v_R_2993_, lean_object* v_a_2994_, lean_object* v_b_2995_, lean_object* v_c_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(v_upperBound_2988_, v_params_2989_, v___x_2990_, v_discr_2991_, v_inst_2992_, v_R_2993_, v_a_2994_, v_b_2995_, v_c_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec(v___x_2990_);
lean_dec_ref(v_params_2989_);
lean_dec(v_upperBound_2988_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(size_t v_sz_3004_, size_t v_i_3005_, lean_object* v_bs_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_sz_3004_, v_i_3005_, v_bs_3006_, v___y_3007_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(lean_object* v_sz_3014_, lean_object* v_i_3015_, lean_object* v_bs_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
size_t v_sz_boxed_3023_; size_t v_i_boxed_3024_; lean_object* v_res_3025_; 
v_sz_boxed_3023_ = lean_unbox_usize(v_sz_3014_);
lean_dec(v_sz_3014_);
v_i_boxed_3024_ = lean_unbox_usize(v_i_3015_);
lean_dec(v_i_3015_);
v_res_3025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(v_sz_boxed_3023_, v_i_boxed_3024_, v_bs_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14(lean_object* v_upperBound_3026_, lean_object* v_fieldInfo_3027_, lean_object* v___x_3028_, lean_object* v_inst_3029_, lean_object* v_R_3030_, lean_object* v_a_3031_, lean_object* v_b_3032_, lean_object* v_c_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___redArg(v_upperBound_3026_, v_fieldInfo_3027_, v___x_3028_, v_a_3031_, v_b_3032_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___boxed(lean_object* v_upperBound_3041_, lean_object* v_fieldInfo_3042_, lean_object* v___x_3043_, lean_object* v_inst_3044_, lean_object* v_R_3045_, lean_object* v_a_3046_, lean_object* v_b_3047_, lean_object* v_c_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14(v_upperBound_3041_, v_fieldInfo_3042_, v___x_3043_, v_inst_3044_, v_R_3045_, v_a_3046_, v_b_3047_, v_c_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___x_3043_);
lean_dec_ref(v_fieldInfo_3042_);
lean_dec(v_upperBound_3041_);
return v_res_3055_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0));
v___x_3058_ = l_Lean_stringToMessageData(v___x_3057_);
return v___x_3058_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2));
v___x_3061_ = l_Lean_stringToMessageData(v___x_3060_);
return v___x_3061_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4));
v___x_3064_ = l_Lean_stringToMessageData(v___x_3063_);
return v___x_3064_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6));
v___x_3067_ = l_Lean_stringToMessageData(v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(lean_object* v_decl_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_toSignature_3075_; lean_object* v_value_3076_; uint8_t v_recursive_3077_; lean_object* v_inlineAttr_x3f_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3210_; 
v_toSignature_3075_ = lean_ctor_get(v_decl_3068_, 0);
v_value_3076_ = lean_ctor_get(v_decl_3068_, 1);
v_recursive_3077_ = lean_ctor_get_uint8(v_decl_3068_, sizeof(void*)*3);
v_inlineAttr_x3f_3078_ = lean_ctor_get(v_decl_3068_, 2);
v_isSharedCheck_3210_ = !lean_is_exclusive(v_decl_3068_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3080_ = v_decl_3068_;
v_isShared_3081_ = v_isSharedCheck_3210_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_inlineAttr_x3f_3078_);
lean_inc(v_value_3076_);
lean_inc(v_toSignature_3075_);
lean_dec(v_decl_3068_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3210_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v_name_3082_; lean_object* v_levelParams_3083_; lean_object* v_type_3084_; lean_object* v_params_3085_; uint8_t v_safe_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3209_; 
v_name_3082_ = lean_ctor_get(v_toSignature_3075_, 0);
v_levelParams_3083_ = lean_ctor_get(v_toSignature_3075_, 1);
v_type_3084_ = lean_ctor_get(v_toSignature_3075_, 2);
v_params_3085_ = lean_ctor_get(v_toSignature_3075_, 3);
v_safe_3086_ = lean_ctor_get_uint8(v_toSignature_3075_, sizeof(void*)*4);
v_isSharedCheck_3209_ = !lean_is_exclusive(v_toSignature_3075_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3088_ = v_toSignature_3075_;
v_isShared_3089_ = v_isSharedCheck_3209_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_params_3085_);
lean_inc(v_type_3084_);
lean_inc(v_levelParams_3083_);
lean_inc(v_name_3082_);
lean_dec(v_toSignature_3075_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3209_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
size_t v_sz_3090_; size_t v___x_3091_; lean_object* v___x_3092_; 
v_sz_3090_ = lean_array_size(v_params_3085_);
v___x_3091_ = ((size_t)0ULL);
lean_inc_ref(v_params_3085_);
v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_3090_, v___x_3091_, v_params_3085_, v_a_3069_, v_a_3071_, v_a_3072_, v_a_3073_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_a_3093_);
lean_dec_ref_known(v___x_3092_, 1);
v___x_3094_ = lean_array_get_size(v_params_3085_);
lean_dec_ref(v_params_3085_);
v___x_3095_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_3084_, v___x_3094_, v_a_3072_, v_a_3073_);
lean_dec_ref(v_type_3084_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3192_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3098_ = v___x_3095_;
v_isShared_3099_ = v_isSharedCheck_3192_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3095_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3192_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3100_; lean_object* v_env_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3100_ = lean_st_ref_get(v_a_3073_);
v_env_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc_ref(v_env_3101_);
lean_dec(v___x_3100_);
v___x_3102_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
lean_inc(v_name_3082_);
v___x_3103_ = l_Lean_TagAttribute_hasTag(v___x_3102_, v_env_3101_, v_name_3082_);
if (lean_obj_tag(v_value_3076_) == 0)
{
lean_object* v_code_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3154_; 
lean_del_object(v___x_3098_);
v_code_3104_ = lean_ctor_get(v_value_3076_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_value_3076_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3106_ = v_value_3076_;
v_isShared_3107_ = v_isSharedCheck_3154_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_code_3104_);
lean_dec(v_value_3076_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3154_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; 
if (v___x_3103_ == 0)
{
v___y_3109_ = v_a_3069_;
v___y_3110_ = v_a_3070_;
v___y_3111_ = v_a_3071_;
v___y_3112_ = v_a_3072_;
v___y_3113_ = v_a_3073_;
goto v___jp_3108_;
}
else
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_del_object(v___x_3106_);
lean_dec_ref(v_code_3104_);
lean_dec(v_a_3096_);
lean_dec(v_a_3093_);
lean_del_object(v___x_3088_);
lean_dec(v_levelParams_3083_);
lean_del_object(v___x_3080_);
lean_dec(v_inlineAttr_x3f_3078_);
v___x_3140_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1);
v___x_3141_ = l_Lean_MessageData_ofName(v_name_3082_);
v___x_3142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3);
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_3144_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3145_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3145_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
v___jp_3108_:
{
lean_object* v___x_3114_; 
v___x_3114_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_3104_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3131_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3131_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3131_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 3, v_a_3093_);
lean_ctor_set(v___x_3088_, 2, v_a_3096_);
v___x_3120_ = v___x_3088_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_name_3082_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v_levelParams_3083_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v_a_3096_);
lean_ctor_set(v_reuseFailAlloc_3130_, 3, v_a_3093_);
lean_ctor_set_uint8(v_reuseFailAlloc_3130_, sizeof(void*)*4, v_safe_3086_);
v___x_3120_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3122_; 
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v_a_3115_);
v___x_3122_ = v___x_3106_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3115_);
v___x_3122_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3124_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 1, v___x_3122_);
lean_ctor_set(v___x_3080_, 0, v___x_3120_);
v___x_3124_ = v___x_3080_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3128_, 2, v_inlineAttr_x3f_3078_);
lean_ctor_set_uint8(v_reuseFailAlloc_3128_, sizeof(void*)*3, v_recursive_3077_);
v___x_3124_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3126_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v___x_3124_);
v___x_3126_ = v___x_3117_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_del_object(v___x_3106_);
lean_dec(v_a_3096_);
lean_dec(v_a_3093_);
lean_del_object(v___x_3088_);
lean_dec(v_levelParams_3083_);
lean_dec(v_name_3082_);
lean_del_object(v___x_3080_);
lean_dec(v_inlineAttr_x3f_3078_);
v_a_3132_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3114_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3114_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
}
}
else
{
lean_object* v_externAttrData_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3191_; 
v_externAttrData_3155_ = lean_ctor_get(v_value_3076_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_value_3076_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3157_ = v_value_3076_;
v_isShared_3158_ = v_isSharedCheck_3191_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_externAttrData_3155_);
lean_dec(v_value_3076_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3191_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v_resultType_3160_; 
if (v___x_3103_ == 0)
{
v_resultType_3160_ = v_a_3096_;
goto v___jp_3159_;
}
else
{
uint8_t v___x_3173_; 
v___x_3173_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_3096_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3174_; 
lean_dec(v_a_3096_);
v___x_3174_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
v_resultType_3160_ = v___x_3174_;
goto v___jp_3159_;
}
else
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_del_object(v___x_3157_);
lean_dec(v_externAttrData_3155_);
lean_del_object(v___x_3098_);
lean_dec(v_a_3093_);
lean_del_object(v___x_3088_);
lean_dec(v_levelParams_3083_);
lean_del_object(v___x_3080_);
lean_dec(v_inlineAttr_x3f_3078_);
v___x_3175_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5);
v___x_3176_ = l_Lean_MessageData_ofName(v_name_3082_);
v___x_3177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3175_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7);
v___x_3179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = l_Lean_MessageData_ofExpr(v_a_3096_);
v___x_3181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3179_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_3181_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
v___jp_3159_:
{
lean_object* v___x_3162_; 
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 3, v_a_3093_);
lean_ctor_set(v___x_3088_, 2, v_resultType_3160_);
v___x_3162_ = v___x_3088_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_name_3082_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_levelParams_3083_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v_resultType_3160_);
lean_ctor_set(v_reuseFailAlloc_3172_, 3, v_a_3093_);
lean_ctor_set_uint8(v_reuseFailAlloc_3172_, sizeof(void*)*4, v_safe_3086_);
v___x_3162_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3164_; 
if (v_isShared_3158_ == 0)
{
v___x_3164_ = v___x_3157_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_externAttrData_3155_);
v___x_3164_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3166_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 1, v___x_3164_);
lean_ctor_set(v___x_3080_, 0, v___x_3162_);
v___x_3166_ = v___x_3080_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_inlineAttr_x3f_3078_);
lean_ctor_set_uint8(v_reuseFailAlloc_3170_, sizeof(void*)*3, v_recursive_3077_);
v___x_3166_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3168_; 
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v___x_3166_);
v___x_3168_ = v___x_3098_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_a_3093_);
lean_del_object(v___x_3088_);
lean_dec(v_levelParams_3083_);
lean_dec(v_name_3082_);
lean_del_object(v___x_3080_);
lean_dec(v_inlineAttr_x3f_3078_);
lean_dec_ref(v_value_3076_);
v_a_3193_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3095_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3095_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_del_object(v___x_3088_);
lean_dec_ref(v_params_3085_);
lean_dec_ref(v_type_3084_);
lean_dec(v_levelParams_3083_);
lean_dec(v_name_3082_);
lean_del_object(v___x_3080_);
lean_dec(v_inlineAttr_x3f_3078_);
lean_dec_ref(v_value_3076_);
v_a_3201_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3092_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3092_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___boxed(lean_object* v_decl_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
lean_dec(v_a_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_a_3212_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(lean_object* v_decl_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3228_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc_n(v_a_3227_, 2);
lean_dec_ref_known(v___x_3226_, 1);
v___x_3228_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_3227_, v_a_3224_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3235_ == 0)
{
lean_object* v_unused_3236_; 
v_unused_3236_ = lean_ctor_get(v___x_3228_, 0);
lean_dec(v_unused_3236_);
v___x_3230_ = v___x_3228_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_dec(v___x_3228_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v_a_3227_);
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3227_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_dec(v_a_3227_);
v_a_3237_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3228_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3228_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
else
{
return v___x_3226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go___boxed(lean_object* v_decl_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
lean_dec(v_a_3250_);
lean_dec_ref(v_a_3249_);
lean_dec(v_a_3248_);
lean_dec_ref(v_a_3247_);
lean_dec(v_a_3246_);
return v_res_3252_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0(void){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3253_ = lean_box(0);
v___x_3254_ = lean_unsigned_to_nat(16u);
v___x_3255_ = lean_mk_array(v___x_3254_, v___x_3253_);
return v___x_3255_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1(void){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3256_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0);
v___x_3257_ = lean_unsigned_to_nat(0u);
v___x_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
lean_ctor_set(v___x_3258_, 1, v___x_3256_);
return v___x_3258_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2(void){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3259_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1);
v___x_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(lean_object* v_decl_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3267_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2);
v___x_3268_ = lean_st_mk_ref(v___x_3267_);
v___x_3269_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_3261_, v___x_3268_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3278_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3278_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3278_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3274_ = lean_st_ref_get(v___x_3268_);
lean_dec(v___x_3268_);
lean_dec(v___x_3274_);
if (v_isShared_3273_ == 0)
{
v___x_3276_ = v___x_3272_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3270_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
else
{
lean_dec(v___x_3268_);
return v___x_3269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___boxed(lean_object* v_decl_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_decl_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
lean_dec(v_a_3283_);
lean_dec_ref(v_a_3282_);
lean_dec(v_a_3281_);
lean_dec_ref(v_a_3280_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(size_t v_sz_3286_, size_t v_i_3287_, lean_object* v_bs_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
uint8_t v___x_3294_; 
v___x_3294_ = lean_usize_dec_lt(v_i_3287_, v_sz_3286_);
if (v___x_3294_ == 0)
{
lean_object* v___x_3295_; 
v___x_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3295_, 0, v_bs_3288_);
return v___x_3295_;
}
else
{
lean_object* v_v_3296_; lean_object* v___x_3297_; lean_object* v_bs_x27_3298_; lean_object* v___x_3299_; 
v_v_3296_ = lean_array_uget(v_bs_3288_, v_i_3287_);
v___x_3297_ = lean_unsigned_to_nat(0u);
v_bs_x27_3298_ = lean_array_uset(v_bs_3288_, v_i_3287_, v___x_3297_);
v___x_3299_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_v_3296_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; size_t v___x_3301_; size_t v___x_3302_; lean_object* v___x_3303_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3299_, 1);
v___x_3301_ = ((size_t)1ULL);
v___x_3302_ = lean_usize_add(v_i_3287_, v___x_3301_);
v___x_3303_ = lean_array_uset(v_bs_x27_3298_, v_i_3287_, v_a_3300_);
v_i_3287_ = v___x_3302_;
v_bs_3288_ = v___x_3303_;
goto _start;
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_dec_ref(v_bs_x27_3298_);
v_a_3305_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3299_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3299_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0___boxed(lean_object* v_sz_3313_, lean_object* v_i_3314_, lean_object* v_bs_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
size_t v_sz_boxed_3321_; size_t v_i_boxed_3322_; lean_object* v_res_3323_; 
v_sz_boxed_3321_ = lean_unbox_usize(v_sz_3313_);
lean_dec(v_sz_3313_);
v_i_boxed_3322_ = lean_unbox_usize(v_i_3314_);
lean_dec(v_i_3314_);
v_res_3323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_boxed_3321_, v_i_boxed_3322_, v_bs_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0(lean_object* v_x_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
size_t v_sz_3330_; size_t v___x_3331_; lean_object* v___x_3332_; 
v_sz_3330_ = lean_array_size(v_x_3324_);
v___x_3331_ = ((size_t)0ULL);
v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_3330_, v___x_3331_, v_x_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0___boxed(lean_object* v_x_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Lean_Compiler_LCNF_toImpure___lam__0(v_x_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3390_; uint8_t v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3390_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3391_ = 1;
v___x_3392_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3393_ = l_Lean_registerTraceClass(v___x_3390_, v___x_3391_, v___x_3392_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2____boxed(lean_object* v_a_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
return v_res_3395_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue = _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue);
res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToImpure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ToImpure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ToImpure(builtin);
}
#ifdef __cplusplus
}
#endif
