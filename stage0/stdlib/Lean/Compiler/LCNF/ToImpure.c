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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_fvarId_362_; lean_object* v_binderName_363_; lean_object* v_type_364_; uint8_t v_borrow_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_421_; 
v_fvarId_362_ = lean_ctor_get(v_p_356_, 0);
v_binderName_363_ = lean_ctor_get(v_p_356_, 1);
v_type_364_ = lean_ctor_get(v_p_356_, 2);
v_borrow_365_ = lean_ctor_get_uint8(v_p_356_, sizeof(void*)*3);
v_isSharedCheck_421_ = !lean_is_exclusive(v_p_356_);
if (v_isSharedCheck_421_ == 0)
{
v___x_367_ = v_p_356_;
v_isShared_368_ = v_isSharedCheck_421_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_type_364_);
lean_inc(v_binderName_363_);
lean_inc(v_fvarId_362_);
lean_dec(v_p_356_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_421_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Compiler_LCNF_toImpureType(v_type_364_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_412_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_412_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_412_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_412_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___y_375_; uint8_t v___y_396_; uint8_t v___x_410_; 
v___x_410_ = l_Lean_Expr_isVoid(v_a_370_);
if (v___x_410_ == 0)
{
uint8_t v___x_411_; 
v___x_411_ = l_Lean_Expr_isErased(v_a_370_);
v___y_396_ = v___x_411_;
goto v___jp_395_;
}
else
{
v___y_396_ = v___x_410_;
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
if (v___y_396_ == 0)
{
v___y_375_ = v_a_358_;
goto v___jp_374_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v_subst_399_; lean_object* v_jpParamMask_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_409_; 
v___x_397_ = lean_box(0);
v___x_398_ = lean_st_ref_take(v_a_357_);
v_subst_399_ = lean_ctor_get(v___x_398_, 0);
v_jpParamMask_400_ = lean_ctor_get(v___x_398_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_409_ == 0)
{
v___x_402_ = v___x_398_;
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_jpParamMask_400_);
lean_inc(v_subst_399_);
lean_dec(v___x_398_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
lean_inc(v_fvarId_362_);
v___x_404_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_399_, v_fvarId_362_, v___x_397_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_jpParamMask_400_);
v___x_406_ = v_reuseFailAlloc_408_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; 
v___x_407_ = lean_st_ref_put(v_a_357_, v___x_406_);
v___y_375_ = v_a_358_;
goto v___jp_374_;
}
}
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_del_object(v___x_367_);
lean_dec(v_binderName_363_);
lean_dec(v_fvarId_362_);
v_a_413_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_369_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_369_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg___boxed(lean_object* v_p_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec(v_a_423_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(lean_object* v_p_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_429_, v_a_430_, v_a_432_, v_a_433_, v_a_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___boxed(lean_object* v_p_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(v_p_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(lean_object* v_00_u03b2_445_, lean_object* v_m_446_, lean_object* v_a_447_, lean_object* v_b_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_m_446_, v_a_447_, v_b_448_);
return v___x_449_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(lean_object* v_00_u03b2_450_, lean_object* v_a_451_, lean_object* v_x_452_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_451_, v_x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___boxed(lean_object* v_00_u03b2_454_, lean_object* v_a_455_, lean_object* v_x_456_){
_start:
{
uint8_t v_res_457_; lean_object* v_r_458_; 
v_res_457_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(v_00_u03b2_454_, v_a_455_, v_x_456_);
lean_dec(v_x_456_);
lean_dec(v_a_455_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1(lean_object* v_00_u03b2_459_, lean_object* v_data_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_data_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2(lean_object* v_00_u03b2_462_, lean_object* v_a_463_, lean_object* v_b_464_, lean_object* v_x_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_463_, v_b_464_, v_x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_467_, lean_object* v_i_468_, lean_object* v_source_469_, lean_object* v_target_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v_i_468_, v_source_469_, v_target_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_x_473_, v_x_474_);
return v___x_475_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_box(0);
v___x_483_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__3));
v___x_484_ = l_Lean_Expr_const___override(v___x_483_, v___x_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg(lean_object* v_upperBound_485_, lean_object* v_a_486_, lean_object* v_b_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
uint8_t v___x_493_; 
v___x_493_ = lean_nat_dec_lt(v_a_486_, v_upperBound_485_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
lean_dec(v_a_486_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v_b_487_);
return v___x_494_;
}
else
{
lean_object* v_fst_495_; lean_object* v_snd_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_533_; 
v_fst_495_ = lean_ctor_get(v_b_487_, 0);
v_snd_496_ = lean_ctor_get(v_b_487_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v_b_487_);
if (v_isSharedCheck_533_ == 0)
{
v___x_498_ = v_b_487_;
v_isShared_499_ = v_isSharedCheck_533_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_snd_496_);
lean_inc(v_fst_495_);
lean_dec(v_b_487_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_533_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__1));
v___x_501_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_500_, v___y_489_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
v___x_503_ = 1;
v___x_504_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4);
v___x_505_ = l_Lean_Compiler_LCNF_spillLinkIdx;
v___x_506_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v_snd_496_);
v___x_507_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_503_, v_a_502_, v___x_504_, v___x_506_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v_fvarId_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v_fvarId_509_ = lean_ctor_get(v_a_508_, 0);
lean_inc(v_fvarId_509_);
v___x_510_ = lean_array_push(v_fst_495_, v_a_508_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v_fvarId_509_);
lean_ctor_set(v___x_498_, 0, v___x_510_);
v___x_512_ = v___x_498_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_fvarId_509_);
v___x_512_ = v_reuseFailAlloc_516_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_add(v_a_486_, v___x_513_);
lean_dec(v_a_486_);
v_a_486_ = v___x_514_;
v_b_487_ = v___x_512_;
goto _start;
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_del_object(v___x_498_);
lean_dec(v_fst_495_);
lean_dec(v_a_486_);
v_a_517_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_507_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_507_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_del_object(v___x_498_);
lean_dec(v_snd_496_);
lean_dec(v_fst_495_);
lean_dec(v_a_486_);
v_a_525_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_501_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_501_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___boxed(lean_object* v_upperBound_534_, lean_object* v_a_535_, lean_object* v_b_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg(v_upperBound_534_, v_a_535_, v_b_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v_upperBound_534_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs(lean_object* v_base_545_, lean_object* v_depth_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; lean_object* v_decls_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_552_ = lean_unsigned_to_nat(0u);
v_decls_553_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs___closed__0));
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v_decls_553_);
lean_ctor_set(v___x_554_, 1, v_base_545_);
v___x_555_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg(v_depth_546_, v___x_552_, v___x_554_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_564_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_564_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_fst_560_; lean_object* v___x_562_; 
v_fst_560_ = lean_ctor_get(v_a_556_, 0);
lean_inc(v_fst_560_);
lean_dec(v_a_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_fst_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_fst_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v_a_565_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_555_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_555_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs___boxed(lean_object* v_base_573_, lean_object* v_depth_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs(v_base_573_, v_depth_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_depth_574_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0(lean_object* v_upperBound_581_, lean_object* v_inst_582_, lean_object* v_R_583_, lean_object* v_a_584_, lean_object* v_b_585_, lean_object* v_c_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg(v_upperBound_581_, v_a_584_, v_b_585_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___boxed(lean_object* v_upperBound_593_, lean_object* v_inst_594_, lean_object* v_R_595_, lean_object* v_a_596_, lean_object* v_b_597_, lean_object* v_c_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0(v_upperBound_593_, v_inst_594_, v_R_595_, v_a_596_, v_b_597_, v_c_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v_upperBound_593_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___redArg(lean_object* v_ctorName_605_, lean_object* v_as_x27_606_, lean_object* v_b_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
if (lean_obj_tag(v_as_x27_606_) == 0)
{
lean_object* v___x_613_; 
lean_dec(v_ctorName_605_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v_b_607_);
return v___x_613_;
}
else
{
lean_object* v_head_614_; lean_object* v_tail_615_; lean_object* v_fst_616_; lean_object* v_snd_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_663_; 
v_head_614_ = lean_ctor_get(v_as_x27_606_, 0);
v_tail_615_ = lean_ctor_get(v_as_x27_606_, 1);
v_fst_616_ = lean_ctor_get(v_b_607_, 0);
v_snd_617_ = lean_ctor_get(v_b_607_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v_b_607_);
if (v_isSharedCheck_663_ == 0)
{
v___x_619_ = v_b_607_;
v_isShared_620_ = v_isSharedCheck_663_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_snd_617_);
lean_inc(v_fst_616_);
lean_dec(v_b_607_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_663_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_nat_add(v_head_614_, v___x_621_);
v___x_623_ = l_Lean_Compiler_LCNF_spillLinkIdx;
v___x_624_ = lean_nat_mul(v___x_622_, v___x_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_array_get_size(v_snd_617_);
lean_inc(v___x_624_);
v___x_626_ = l_Array_extract___redArg(v_snd_617_, v___x_624_, v___x_625_);
v___x_627_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__1));
v___x_628_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_627_, v___y_609_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
v___x_630_ = 1;
v___x_631_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4);
v___x_632_ = lean_array_get_size(v___x_626_);
lean_inc(v_ctorName_605_);
v___x_633_ = l_Lean_Compiler_LCNF_spillCtorInfo(v_ctorName_605_, v___x_632_);
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_626_);
v___x_635_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_630_, v_a_629_, v___x_631_, v___x_634_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v_fvarId_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v_fvarId_637_ = lean_ctor_get(v_a_636_, 0);
lean_inc(v_fvarId_637_);
v___x_638_ = lean_array_push(v_fst_616_, v_a_636_);
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = l_Array_extract___redArg(v_snd_617_, v___x_639_, v___x_624_);
lean_dec(v_snd_617_);
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v_fvarId_637_);
v___x_642_ = lean_array_push(v___x_640_, v___x_641_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_642_);
lean_ctor_set(v___x_619_, 0, v___x_638_);
v___x_644_ = v___x_619_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_642_);
v___x_644_ = v_reuseFailAlloc_646_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
v_as_x27_606_ = v_tail_615_;
v_b_607_ = v___x_644_;
goto _start;
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v___x_624_);
lean_del_object(v___x_619_);
lean_dec(v_snd_617_);
lean_dec(v_fst_616_);
lean_dec(v_ctorName_605_);
v_a_647_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_635_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_635_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v___x_626_);
lean_dec(v___x_624_);
lean_del_object(v___x_619_);
lean_dec(v_snd_617_);
lean_dec(v_fst_616_);
lean_dec(v_ctorName_605_);
v_a_655_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_628_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_628_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___redArg___boxed(lean_object* v_ctorName_664_, lean_object* v_as_x27_665_, lean_object* v_b_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___redArg(v_ctorName_664_, v_as_x27_665_, v_b_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v_as_x27_665_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs(lean_object* v_ctorName_673_, lean_object* v_objArgs_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_decls_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v_decls_680_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs___closed__0));
v___x_681_ = lean_array_get_size(v_objArgs_674_);
v___x_682_ = l_Lean_Compiler_LCNF_numSpillObjs(v___x_681_);
v___x_683_ = l_List_range(v___x_682_);
v___x_684_ = l_List_reverse___redArg(v___x_683_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v_decls_680_);
lean_ctor_set(v___x_685_, 1, v_objArgs_674_);
v___x_686_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___redArg(v_ctorName_673_, v___x_684_, v___x_685_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
lean_dec(v___x_684_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_703_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_703_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_703_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_703_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_fst_691_; lean_object* v_snd_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_702_; 
v_fst_691_ = lean_ctor_get(v_a_687_, 0);
v_snd_692_ = lean_ctor_get(v_a_687_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_a_687_);
if (v_isSharedCheck_702_ == 0)
{
v___x_694_ = v_a_687_;
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_snd_692_);
lean_inc(v_fst_691_);
lean_dec(v_a_687_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_fst_691_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_snd_692_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_697_);
v___x_699_ = v___x_689_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
else
{
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs___boxed(lean_object* v_ctorName_704_, lean_object* v_objArgs_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs(v_ctorName_704_, v_objArgs_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0(lean_object* v_ctorName_712_, lean_object* v_as_713_, lean_object* v_as_x27_714_, lean_object* v_b_715_, lean_object* v_a_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___redArg(v_ctorName_712_, v_as_x27_714_, v_b_715_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0___boxed(lean_object* v_ctorName_723_, lean_object* v_as_724_, lean_object* v_as_x27_725_, lean_object* v_b_726_, lean_object* v_a_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs_spec__0(v_ctorName_723_, v_as_724_, v_as_x27_725_, v_b_726_, v_a_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v_as_x27_725_);
lean_dec(v_as_724_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls_spec__0(lean_object* v_as_734_, size_t v_i_735_, size_t v_stop_736_, lean_object* v_b_737_){
_start:
{
uint8_t v___x_738_; 
v___x_738_ = lean_usize_dec_eq(v_i_735_, v_stop_736_);
if (v___x_738_ == 0)
{
size_t v___x_739_; size_t v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_sub(v_i_735_, v___x_739_);
v___x_741_ = lean_array_uget_borrowed(v_as_734_, v___x_740_);
lean_inc(v___x_741_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v_b_737_);
v_i_735_ = v___x_740_;
v_b_737_ = v___x_742_;
goto _start;
}
else
{
return v_b_737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls_spec__0___boxed(lean_object* v_as_744_, lean_object* v_i_745_, lean_object* v_stop_746_, lean_object* v_b_747_){
_start:
{
size_t v_i_boxed_748_; size_t v_stop_boxed_749_; lean_object* v_res_750_; 
v_i_boxed_748_ = lean_unbox_usize(v_i_745_);
lean_dec(v_i_745_);
v_stop_boxed_749_ = lean_unbox_usize(v_stop_746_);
lean_dec(v_stop_746_);
v_res_750_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls_spec__0(v_as_744_, v_i_boxed_748_, v_stop_boxed_749_, v_b_747_);
lean_dec_ref(v_as_744_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls(lean_object* v_decls_751_, lean_object* v_code_752_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_753_ = lean_array_get_size(v_decls_751_);
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = lean_nat_dec_lt(v___x_754_, v___x_753_);
if (v___x_755_ == 0)
{
return v_code_752_;
}
else
{
size_t v___x_756_; size_t v___x_757_; lean_object* v___x_758_; 
v___x_756_ = lean_usize_of_nat(v___x_753_);
v___x_757_ = ((size_t)0ULL);
v___x_758_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls_spec__0(v_decls_751_, v___x_756_, v___x_757_, v_code_752_);
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls___boxed(lean_object* v_decls_759_, lean_object* v_code_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls(v_decls_759_, v_code_760_);
lean_dec_ref(v_decls_759_);
return v_res_761_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_box(0);
v___x_766_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_767_ = l_Lean_Expr_const___override(v___x_766_, v___x_765_);
return v___x_767_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2);
v___x_769_ = lean_box(1);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_768_);
return v___x_770_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_box(0);
v___x_775_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5));
v___x_776_ = l_Lean_Expr_const___override(v___x_775_, v___x_774_);
return v___x_776_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = lean_box(0);
v___x_781_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8));
v___x_782_ = l_Lean_Expr_const___override(v___x_781_, v___x_780_);
return v___x_782_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9);
v___x_784_ = lean_box(1);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v___x_783_);
return v___x_785_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__11(void){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Compiler_LCNF_instInhabitedLetDecl_default___redArg();
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(lean_object* v_base_787_, lean_object* v_spills_788_, lean_object* v_ctorInfo_789_, lean_object* v_field_790_){
_start:
{
switch(lean_obj_tag(v_field_790_))
{
case 0:
{
lean_object* v___x_791_; 
lean_dec(v_base_787_);
v___x_791_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3);
return v___x_791_;
}
case 1:
{
lean_object* v_i_792_; lean_object* v_type_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_i_792_ = lean_ctor_get(v_field_790_, 0);
v_type_793_ = lean_ctor_get(v_field_790_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_field_790_);
if (v_isSharedCheck_801_ == 0)
{
v___x_795_ = v_field_790_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_type_793_);
lean_inc(v_i_792_);
lean_dec(v_field_790_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 6);
lean_ctor_set(v___x_795_, 1, v_base_787_);
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_i_792_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_base_787_);
v___x_798_ = v_reuseFailAlloc_800_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v_type_793_);
return v___x_799_;
}
}
}
case 2:
{
lean_object* v_i_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_i_802_ = lean_ctor_get(v_field_790_, 0);
lean_inc(v_i_802_);
lean_dec_ref_known(v_field_790_, 1);
v___x_803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_803_, 0, v_i_802_);
lean_ctor_set(v___x_803_, 1, v_base_787_);
v___x_804_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
return v___x_805_;
}
case 3:
{
lean_object* v_offset_806_; lean_object* v_type_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_818_; 
v_offset_806_ = lean_ctor_get(v_field_790_, 1);
v_type_807_ = lean_ctor_get(v_field_790_, 2);
v_isSharedCheck_818_ = !lean_is_exclusive(v_field_790_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_field_790_, 0);
lean_dec(v_unused_819_);
v___x_809_ = v_field_790_;
v_isShared_810_ = v_isSharedCheck_818_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_type_807_);
lean_inc(v_offset_806_);
lean_dec(v_field_790_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_818_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_size_811_; lean_object* v_usize_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
v_size_811_ = lean_ctor_get(v_ctorInfo_789_, 2);
v_usize_812_ = lean_ctor_get(v_ctorInfo_789_, 3);
v___x_813_ = lean_nat_add(v_size_811_, v_usize_812_);
if (v_isShared_810_ == 0)
{
lean_ctor_set_tag(v___x_809_, 8);
lean_ctor_set(v___x_809_, 2, v_base_787_);
lean_ctor_set(v___x_809_, 0, v___x_813_);
v___x_815_ = v___x_809_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_offset_806_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_base_787_);
v___x_815_ = v_reuseFailAlloc_817_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; 
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v_type_807_);
return v___x_816_;
}
}
}
case 4:
{
lean_object* v___x_820_; 
lean_dec(v_base_787_);
v___x_820_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10);
return v___x_820_;
}
default: 
{
lean_object* v_depth_821_; lean_object* v_i_822_; lean_object* v_type_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v_fvarId_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec(v_base_787_);
v_depth_821_ = lean_ctor_get(v_field_790_, 0);
lean_inc(v_depth_821_);
v_i_822_ = lean_ctor_get(v_field_790_, 1);
lean_inc(v_i_822_);
v_type_823_ = lean_ctor_get(v_field_790_, 2);
lean_inc_ref(v_type_823_);
lean_dec_ref_known(v_field_790_, 3);
v___x_824_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__11);
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = lean_nat_sub(v_depth_821_, v___x_825_);
lean_dec(v_depth_821_);
v___x_827_ = lean_array_get_borrowed(v___x_824_, v_spills_788_, v___x_826_);
lean_dec(v___x_826_);
v_fvarId_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_fvarId_828_);
v___x_829_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_829_, 0, v_i_822_);
lean_ctor_set(v___x_829_, 1, v_fvarId_828_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v_type_823_);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___boxed(lean_object* v_base_831_, lean_object* v_spills_832_, lean_object* v_ctorInfo_833_, lean_object* v_field_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_base_831_, v_spills_832_, v_ctorInfo_833_, v_field_834_);
lean_dec_ref(v_ctorInfo_833_);
lean_dec_ref(v_spills_832_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(lean_object* v_arg_836_, lean_object* v_a_837_){
_start:
{
uint8_t v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v_subst_842_; lean_object* v___x_843_; 
v___x_839_ = 0;
v___x_840_ = 1;
v___x_841_ = lean_st_ref_get(v_a_837_);
v_subst_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc_ref(v_subst_842_);
lean_dec(v___x_841_);
v___x_843_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v___x_839_, v_subst_842_, v_arg_836_, v___x_840_);
lean_dec_ref(v_subst_842_);
if (lean_obj_tag(v___x_843_) == 1)
{
lean_object* v_fvarId_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_852_; 
v_fvarId_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_852_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_fvarId_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_fvarId_844_);
v___x_849_ = v_reuseFailAlloc_851_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; 
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec(v___x_843_);
v___x_853_ = lean_box(0);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg___boxed(lean_object* v_arg_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_855_, v_a_856_);
lean_dec(v_a_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(lean_object* v_arg_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_859_, v_a_860_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___boxed(lean_object* v_arg_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(v_arg_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(lean_object* v_msg_875_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = l_Lean_instInhabitedExpr;
v___x_877_ = lean_panic_fn_borrowed(v___x_876_, v_msg_875_);
return v___x_877_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_881_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2));
v___x_882_ = lean_unsigned_to_nat(11u);
v___x_883_ = lean_unsigned_to_nat(115u);
v___x_884_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1));
v___x_885_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_886_ = l_mkPanicMessageWithDecl(v___x_885_, v___x_884_, v___x_883_, v___x_882_, v___x_881_);
return v___x_886_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = lean_box(0);
v___x_888_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_889_ = l_Lean_mkConst(v___x_888_, v___x_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(lean_object* v_type_890_, lean_object* v_arity_891_){
_start:
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_nat_dec_eq(v_arity_891_, v___x_895_);
if (v___x_896_ == 0)
{
switch(lean_obj_tag(v_type_890_))
{
case 7:
{
lean_object* v_body_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_body_897_ = lean_ctor_get(v_type_890_, 2);
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_nat_sub(v_arity_891_, v___x_898_);
lean_dec(v_arity_891_);
v_type_890_ = v_body_897_;
v_arity_891_ = v___x_899_;
goto _start;
}
case 4:
{
lean_object* v_declName_901_; 
lean_dec(v_arity_891_);
v_declName_901_ = lean_ctor_get(v_type_890_, 0);
if (lean_obj_tag(v_declName_901_) == 1)
{
lean_object* v_pre_902_; 
v_pre_902_ = lean_ctor_get(v_declName_901_, 0);
if (lean_obj_tag(v_pre_902_) == 0)
{
lean_object* v_str_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_str_903_ = lean_ctor_get(v_declName_901_, 1);
v___x_904_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0));
v___x_905_ = lean_string_dec_eq(v_str_903_, v___x_904_);
if (v___x_905_ == 0)
{
goto v___jp_892_;
}
else
{
lean_object* v___x_906_; 
v___x_906_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4);
return v___x_906_;
}
}
else
{
goto v___jp_892_;
}
}
else
{
goto v___jp_892_;
}
}
default: 
{
lean_dec(v_arity_891_);
goto v___jp_892_;
}
}
}
else
{
lean_dec(v_arity_891_);
lean_inc_ref(v_type_890_);
return v_type_890_;
}
v___jp_892_:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3);
v___x_894_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(v___x_893_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___boxed(lean_object* v_type_907_, lean_object* v_arity_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_907_, v_arity_908_);
lean_dec_ref(v_type_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object* v_type_910_, lean_object* v_arity_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_910_, v_arity_911_);
v___x_916_ = l_Lean_Compiler_LCNF_toImpureType(v___x_915_, v_a_912_, v_a_913_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType___boxed(lean_object* v_type_917_, lean_object* v_arity_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_917_, v_arity_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec_ref(v_type_917_);
return v_res_922_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_box(0);
v___x_927_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1));
v___x_928_ = l_Lean_Expr_const___override(v___x_927_, v___x_926_);
return v___x_928_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_box(0);
v___x_933_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4));
v___x_934_ = l_Lean_Expr_const___override(v___x_933_, v___x_932_);
return v___x_934_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = lean_box(0);
v___x_939_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7));
v___x_940_ = l_Lean_Expr_const___override(v___x_939_, v___x_938_);
return v___x_940_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_box(0);
v___x_945_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10));
v___x_946_ = l_Lean_Expr_const___override(v___x_945_, v___x_944_);
return v___x_946_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = lean_box(0);
v___x_951_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13));
v___x_952_ = l_Lean_Expr_const___override(v___x_951_, v___x_950_);
return v___x_952_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = lean_box(0);
v___x_957_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16));
v___x_958_ = l_Lean_Expr_const___override(v___x_957_, v___x_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(lean_object* v_v_959_){
_start:
{
switch(lean_obj_tag(v_v_959_))
{
case 0:
{
lean_object* v_val_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_val_960_ = lean_ctor_get(v_v_959_, 0);
v___x_961_ = lean_cstr_to_nat("4294967296");
v___x_962_ = lean_nat_dec_lt(v_val_960_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
v___x_963_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
return v___x_963_;
}
else
{
lean_object* v___x_964_; 
v___x_964_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
return v___x_964_;
}
}
case 1:
{
lean_object* v___x_965_; 
v___x_965_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4);
return v___x_965_;
}
case 2:
{
lean_object* v___x_966_; 
v___x_966_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
return v___x_966_;
}
case 3:
{
lean_object* v___x_967_; 
v___x_967_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11);
return v___x_967_;
}
case 4:
{
lean_object* v___x_968_; 
v___x_968_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14);
return v___x_968_;
}
case 5:
{
lean_object* v___x_969_; 
v___x_969_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17);
return v___x_969_;
}
default: 
{
lean_object* v___x_970_; 
v___x_970_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___boxed(lean_object* v_v_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_v_971_);
lean_dec_ref(v_v_971_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(lean_object* v_as_973_, size_t v_i_974_, size_t v_stop_975_, lean_object* v_b_976_){
_start:
{
lean_object* v___y_978_; uint8_t v___x_982_; 
v___x_982_ = lean_usize_dec_eq(v_i_974_, v_stop_975_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v_snd_984_; uint8_t v___x_985_; 
v___x_983_ = lean_array_uget_borrowed(v_as_973_, v_i_974_);
v_snd_984_ = lean_ctor_get(v___x_983_, 1);
v___x_985_ = lean_unbox(v_snd_984_);
if (v___x_985_ == 0)
{
v___y_978_ = v_b_976_;
goto v___jp_977_;
}
else
{
lean_object* v_fst_986_; lean_object* v___x_987_; 
v_fst_986_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_fst_986_);
v___x_987_ = lean_array_push(v_b_976_, v_fst_986_);
v___y_978_ = v___x_987_;
goto v___jp_977_;
}
}
else
{
return v_b_976_;
}
v___jp_977_:
{
size_t v___x_979_; size_t v___x_980_; 
v___x_979_ = ((size_t)1ULL);
v___x_980_ = lean_usize_add(v_i_974_, v___x_979_);
v_i_974_ = v___x_980_;
v_b_976_ = v___y_978_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4___boxed(lean_object* v_as_988_, lean_object* v_i_989_, lean_object* v_stop_990_, lean_object* v_b_991_){
_start:
{
size_t v_i_boxed_992_; size_t v_stop_boxed_993_; lean_object* v_res_994_; 
v_i_boxed_992_ = lean_unbox_usize(v_i_989_);
lean_dec(v_i_989_);
v_stop_boxed_993_ = lean_unbox_usize(v_stop_990_);
lean_dec(v_stop_990_);
v_res_994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v_as_988_, v_i_boxed_992_, v_stop_boxed_993_, v_b_991_);
lean_dec_ref(v_as_988_);
return v_res_994_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(lean_object* v_msg_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v_toApplicative_1004_; lean_object* v_toFunctor_1005_; lean_object* v_toSeq_1006_; lean_object* v_toSeqLeft_1007_; lean_object* v_toSeqRight_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v_toApplicative_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1052_; 
v___x_1003_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_1004_ = lean_ctor_get(v___x_1003_, 0);
v_toFunctor_1005_ = lean_ctor_get(v_toApplicative_1004_, 0);
v_toSeq_1006_ = lean_ctor_get(v_toApplicative_1004_, 2);
v_toSeqLeft_1007_ = lean_ctor_get(v_toApplicative_1004_, 3);
v_toSeqRight_1008_ = lean_ctor_get(v_toApplicative_1004_, 4);
v___f_1009_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_1010_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref_n(v_toFunctor_1005_, 2);
v___f_1011_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1011_, 0, v_toFunctor_1005_);
v___f_1012_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1012_, 0, v_toFunctor_1005_);
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___f_1011_);
lean_ctor_set(v___x_1013_, 1, v___f_1012_);
lean_inc(v_toSeqRight_1008_);
v___f_1014_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1014_, 0, v_toSeqRight_1008_);
lean_inc(v_toSeqLeft_1007_);
v___f_1015_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1015_, 0, v_toSeqLeft_1007_);
lean_inc(v_toSeq_1006_);
v___f_1016_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1016_, 0, v_toSeq_1006_);
v___x_1017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1013_);
lean_ctor_set(v___x_1017_, 1, v___f_1009_);
lean_ctor_set(v___x_1017_, 2, v___f_1016_);
lean_ctor_set(v___x_1017_, 3, v___f_1015_);
lean_ctor_set(v___x_1017_, 4, v___f_1014_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___f_1010_);
v___x_1019_ = l_StateRefT_x27_instMonad___redArg(v___x_1018_);
v_toApplicative_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v___x_1019_, 1);
lean_dec(v_unused_1053_);
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1052_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_toApplicative_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1052_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v_toFunctor_1024_; lean_object* v_toSeq_1025_; lean_object* v_toSeqLeft_1026_; lean_object* v_toSeqRight_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1050_; 
v_toFunctor_1024_ = lean_ctor_get(v_toApplicative_1020_, 0);
v_toSeq_1025_ = lean_ctor_get(v_toApplicative_1020_, 2);
v_toSeqLeft_1026_ = lean_ctor_get(v_toApplicative_1020_, 3);
v_toSeqRight_1027_ = lean_ctor_get(v_toApplicative_1020_, 4);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_toApplicative_1020_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v_toApplicative_1020_, 1);
lean_dec(v_unused_1051_);
v___x_1029_ = v_toApplicative_1020_;
v_isShared_1030_ = v_isSharedCheck_1050_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_toSeqRight_1027_);
lean_inc(v_toSeqLeft_1026_);
lean_inc(v_toSeq_1025_);
lean_inc(v_toFunctor_1024_);
lean_dec(v_toApplicative_1020_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1050_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___f_1034_; lean_object* v___x_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___x_1040_; 
v___f_1031_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_1032_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_1024_);
v___f_1033_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1033_, 0, v_toFunctor_1024_);
v___f_1034_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1034_, 0, v_toFunctor_1024_);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___f_1033_);
lean_ctor_set(v___x_1035_, 1, v___f_1034_);
v___f_1036_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1036_, 0, v_toSeqRight_1027_);
v___f_1037_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1037_, 0, v_toSeqLeft_1026_);
v___f_1038_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1038_, 0, v_toSeq_1025_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 4, v___f_1036_);
lean_ctor_set(v___x_1029_, 3, v___f_1037_);
lean_ctor_set(v___x_1029_, 2, v___f_1038_);
lean_ctor_set(v___x_1029_, 1, v___f_1031_);
lean_ctor_set(v___x_1029_, 0, v___x_1035_);
v___x_1040_ = v___x_1029_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___f_1031_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v___f_1038_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v___f_1037_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v___f_1036_);
v___x_1040_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1042_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 1, v___f_1032_);
lean_ctor_set(v___x_1022_, 0, v___x_1040_);
v___x_1042_ = v___x_1022_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___f_1032_);
v___x_1042_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_37405__overap_1046_; lean_object* v___x_1047_; 
v___x_1043_ = l_StateRefT_x27_instMonad___redArg(v___x_1042_);
v___x_1044_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0);
v___x_1045_ = l_instInhabitedOfMonad___redArg(v___x_1043_, v___x_1044_);
v___x_37405__overap_1046_ = lean_panic_fn_borrowed(v___x_1045_, v_msg_996_);
lean_dec(v___x_1045_);
lean_inc(v___y_1001_);
lean_inc_ref(v___y_1000_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
lean_inc(v___y_997_);
v___x_1047_ = lean_apply_6(v___x_37405__overap_1046_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, lean_box(0));
return v___x_1047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(lean_object* v_msg_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v_msg_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_spec__10(lean_object* v_as_1062_, size_t v_i_1063_, size_t v_stop_1064_, lean_object* v_b_1065_){
_start:
{
lean_object* v___y_1067_; uint8_t v___x_1071_; 
v___x_1071_ = lean_usize_dec_eq(v_i_1063_, v_stop_1064_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = lean_array_uget_borrowed(v_as_1062_, v_i_1063_);
v___x_1073_ = l_Lean_Compiler_LCNF_CtorFieldInfo_spillDepth(v___x_1072_);
v___x_1074_ = lean_nat_dec_le(v_b_1065_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_dec(v___x_1073_);
v___y_1067_ = v_b_1065_;
goto v___jp_1066_;
}
else
{
lean_dec(v_b_1065_);
v___y_1067_ = v___x_1073_;
goto v___jp_1066_;
}
}
else
{
return v_b_1065_;
}
v___jp_1066_:
{
size_t v___x_1068_; size_t v___x_1069_; 
v___x_1068_ = ((size_t)1ULL);
v___x_1069_ = lean_usize_add(v_i_1063_, v___x_1068_);
v_i_1063_ = v___x_1069_;
v_b_1065_ = v___y_1067_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_spec__10___boxed(lean_object* v_as_1075_, lean_object* v_i_1076_, lean_object* v_stop_1077_, lean_object* v_b_1078_){
_start:
{
size_t v_i_boxed_1079_; size_t v_stop_boxed_1080_; lean_object* v_res_1081_; 
v_i_boxed_1079_ = lean_unbox_usize(v_i_1076_);
lean_dec(v_i_1076_);
v_stop_boxed_1080_ = lean_unbox_usize(v_stop_1077_);
lean_dec(v_stop_1077_);
v_res_1081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_spec__10(v_as_1075_, v_i_boxed_1079_, v_stop_boxed_1080_, v_b_1078_);
lean_dec_ref(v_as_1075_);
return v_res_1081_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(lean_object* v_upperBound_1083_, lean_object* v_params_1084_, lean_object* v___x_1085_, lean_object* v_discr_1086_, lean_object* v_a_1087_, lean_object* v_b_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_a_1092_; uint8_t v___x_1096_; 
v___x_1096_ = lean_nat_dec_lt(v_a_1087_, v_upperBound_1083_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_dec(v_a_1087_);
lean_dec(v_discr_1086_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_b_1088_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1098_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0);
v___x_1099_ = lean_box(0);
v___x_1100_ = lean_array_get_borrowed(v___x_1098_, v_params_1084_, v_a_1087_);
v___x_1101_ = lean_nat_dec_eq(v_a_1087_, v___x_1085_);
if (v___x_1101_ == 0)
{
lean_object* v_fvarId_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_subst_1105_; lean_object* v_jpParamMask_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1115_; 
v_fvarId_1102_ = lean_ctor_get(v___x_1100_, 0);
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_st_ref_take(v___y_1089_);
v_subst_1105_ = lean_ctor_get(v___x_1104_, 0);
v_jpParamMask_1106_ = lean_ctor_get(v___x_1104_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1108_ = v___x_1104_;
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_jpParamMask_1106_);
lean_inc(v_subst_1105_);
lean_dec(v___x_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; 
lean_inc(v_fvarId_1102_);
v___x_1110_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1105_, v_fvarId_1102_, v___x_1103_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1110_);
v___x_1112_ = v___x_1108_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_jpParamMask_1106_);
v___x_1112_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_st_ref_put(v___y_1089_, v___x_1112_);
v_a_1092_ = v___x_1099_;
goto v___jp_1091_;
}
}
}
else
{
lean_object* v_fvarId_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v_subst_1119_; lean_object* v_jpParamMask_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1129_; 
v_fvarId_1116_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_discr_1086_);
v___x_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_discr_1086_);
v___x_1118_ = lean_st_ref_take(v___y_1089_);
v_subst_1119_ = lean_ctor_get(v___x_1118_, 0);
v_jpParamMask_1120_ = lean_ctor_get(v___x_1118_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1122_ = v___x_1118_;
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_jpParamMask_1120_);
lean_inc(v_subst_1119_);
lean_dec(v___x_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_inc(v_fvarId_1116_);
v___x_1124_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1119_, v_fvarId_1116_, v___x_1117_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_jpParamMask_1120_);
v___x_1126_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_st_ref_put(v___y_1089_, v___x_1126_);
v_a_1092_ = v___x_1099_;
goto v___jp_1091_;
}
}
}
}
v___jp_1091_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_add(v_a_1087_, v___x_1093_);
lean_dec(v_a_1087_);
v_a_1087_ = v___x_1094_;
v_b_1088_ = v_a_1092_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(lean_object* v_upperBound_1130_, lean_object* v_params_1131_, lean_object* v___x_1132_, lean_object* v_discr_1133_, lean_object* v_a_1134_, lean_object* v_b_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_1130_, v_params_1131_, v___x_1132_, v_discr_1133_, v_a_1134_, v_b_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec(v___x_1132_);
lean_dec_ref(v_params_1131_);
lean_dec(v_upperBound_1130_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(size_t v_sz_1139_, size_t v_i_1140_, lean_object* v_bs_1141_){
_start:
{
uint8_t v___x_1142_; 
v___x_1142_ = lean_usize_dec_lt(v_i_1140_, v_sz_1139_);
if (v___x_1142_ == 0)
{
return v_bs_1141_;
}
else
{
lean_object* v_v_1143_; lean_object* v_type_1144_; lean_object* v___x_1145_; lean_object* v_bs_x27_1146_; uint8_t v___y_1148_; uint8_t v___y_1155_; uint8_t v___x_1157_; 
v_v_1143_ = lean_array_uget_borrowed(v_bs_1141_, v_i_1140_);
v_type_1144_ = lean_ctor_get(v_v_1143_, 2);
lean_inc_ref(v_type_1144_);
v___x_1145_ = lean_unsigned_to_nat(0u);
v_bs_x27_1146_ = lean_array_uset(v_bs_1141_, v_i_1140_, v___x_1145_);
v___x_1157_ = l_Lean_Expr_isVoid(v_type_1144_);
if (v___x_1157_ == 0)
{
uint8_t v___x_1158_; 
v___x_1158_ = l_Lean_Expr_isErased(v_type_1144_);
lean_dec_ref(v_type_1144_);
v___y_1155_ = v___x_1158_;
goto v___jp_1154_;
}
else
{
lean_dec_ref(v_type_1144_);
v___y_1155_ = v___x_1157_;
goto v___jp_1154_;
}
v___jp_1147_:
{
size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1149_ = ((size_t)1ULL);
v___x_1150_ = lean_usize_add(v_i_1140_, v___x_1149_);
v___x_1151_ = lean_box(v___y_1148_);
v___x_1152_ = lean_array_uset(v_bs_x27_1146_, v_i_1140_, v___x_1151_);
v_i_1140_ = v___x_1150_;
v_bs_1141_ = v___x_1152_;
goto _start;
}
v___jp_1154_:
{
if (v___y_1155_ == 0)
{
v___y_1148_ = v___x_1142_;
goto v___jp_1147_;
}
else
{
uint8_t v___x_1156_; 
v___x_1156_ = 0;
v___y_1148_ = v___x_1156_;
goto v___jp_1147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object* v_sz_1159_, lean_object* v_i_1160_, lean_object* v_bs_1161_){
_start:
{
size_t v_sz_boxed_1162_; size_t v_i_boxed_1163_; lean_object* v_res_1164_; 
v_sz_boxed_1162_ = lean_unbox_usize(v_sz_1159_);
lean_dec(v_sz_1159_);
v_i_boxed_1163_ = lean_unbox_usize(v_i_1160_);
lean_dec(v_i_1160_);
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_boxed_1162_, v_i_boxed_1163_, v_bs_1161_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(size_t v_sz_1165_, size_t v_i_1166_, lean_object* v_bs_1167_, lean_object* v___y_1168_){
_start:
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_usize_dec_lt(v_i_1166_, v_sz_1165_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_bs_1167_);
return v___x_1171_;
}
else
{
lean_object* v_v_1172_; lean_object* v___x_1173_; lean_object* v_bs_x27_1174_; lean_object* v___x_1175_; 
v_v_1172_ = lean_array_uget(v_bs_1167_, v_i_1166_);
v___x_1173_ = lean_unsigned_to_nat(0u);
v_bs_x27_1174_ = lean_array_uset(v_bs_1167_, v_i_1166_, v___x_1173_);
v___x_1175_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_v_1172_, v___y_1168_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; size_t v___x_1177_; size_t v___x_1178_; lean_object* v___x_1179_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
v___x_1177_ = ((size_t)1ULL);
v___x_1178_ = lean_usize_add(v_i_1166_, v___x_1177_);
v___x_1179_ = lean_array_uset(v_bs_x27_1174_, v_i_1166_, v_a_1176_);
v_i_1166_ = v___x_1178_;
v_bs_1167_ = v___x_1179_;
goto _start;
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref(v_bs_x27_1174_);
v_a_1181_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1175_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1175_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(lean_object* v_sz_1189_, lean_object* v_i_1190_, lean_object* v_bs_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
size_t v_sz_boxed_1194_; size_t v_i_boxed_1195_; lean_object* v_res_1196_; 
v_sz_boxed_1194_ = lean_unbox_usize(v_sz_1189_);
lean_dec(v_sz_1189_);
v_i_boxed_1195_ = lean_unbox_usize(v_i_1190_);
lean_dec(v_i_1190_);
v_res_1196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_sz_boxed_1194_, v_i_boxed_1195_, v_bs_1191_, v___y_1192_);
lean_dec(v___y_1192_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___redArg(lean_object* v_upperBound_1197_, lean_object* v_fieldInfo_1198_, lean_object* v___x_1199_, lean_object* v_a_1200_, lean_object* v_b_1201_){
_start:
{
lean_object* v_a_1204_; uint8_t v___x_1208_; 
v___x_1208_ = lean_nat_dec_lt(v_a_1200_, v_upperBound_1197_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; 
lean_dec(v_a_1200_);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v_b_1201_);
return v___x_1209_;
}
else
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_array_fget_borrowed(v_fieldInfo_1198_, v_a_1200_);
switch(lean_obj_tag(v___x_1210_))
{
case 1:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = lean_array_get_borrowed(v___x_1211_, v___x_1199_, v_a_1200_);
lean_inc(v___x_1212_);
v___x_1213_ = lean_array_push(v_b_1201_, v___x_1212_);
v_a_1204_ = v___x_1213_;
goto v___jp_1203_;
}
case 5:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_array_get_borrowed(v___x_1214_, v___x_1199_, v_a_1200_);
lean_inc(v___x_1215_);
v___x_1216_ = lean_array_push(v_b_1201_, v___x_1215_);
v_a_1204_ = v___x_1216_;
goto v___jp_1203_;
}
default: 
{
v_a_1204_ = v_b_1201_;
goto v___jp_1203_;
}
}
}
v___jp_1203_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_unsigned_to_nat(1u);
v___x_1206_ = lean_nat_add(v_a_1200_, v___x_1205_);
lean_dec(v_a_1200_);
v_a_1200_ = v___x_1206_;
v_b_1201_ = v_a_1204_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___redArg___boxed(lean_object* v_upperBound_1217_, lean_object* v_fieldInfo_1218_, lean_object* v___x_1219_, lean_object* v_a_1220_, lean_object* v_b_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___redArg(v_upperBound_1217_, v_fieldInfo_1218_, v___x_1219_, v_a_1220_, v_b_1221_);
lean_dec_ref(v___x_1219_);
lean_dec_ref(v_fieldInfo_1218_);
lean_dec(v_upperBound_1217_);
return v_res_1223_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__0);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1227_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1228_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__1);
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
lean_ctor_set(v___x_1230_, 2, v___x_1229_);
lean_ctor_set(v___x_1230_, 3, v___x_1229_);
lean_ctor_set(v___x_1230_, 4, v___x_1228_);
lean_ctor_set(v___x_1230_, 5, v___x_1228_);
lean_ctor_set(v___x_1230_, 6, v___x_1228_);
lean_ctor_set(v___x_1230_, 7, v___x_1228_);
lean_ctor_set(v___x_1230_, 8, v___x_1228_);
lean_ctor_set(v___x_1230_, 9, v___x_1228_);
lean_ctor_set(v___x_1230_, 10, v___x_1228_);
lean_ctor_set(v___x_1230_, 11, v___x_1227_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(lean_object* v_msg_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_ref_1237_; lean_object* v___x_1238_; lean_object* v_env_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_ref_1237_ = lean_ctor_get(v___y_1234_, 2);
v___x_1238_ = lean_st_ref_get(v___y_1235_);
v_env_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc_ref(v_env_1239_);
lean_dec(v___x_1238_);
v___x_1240_ = lean_st_ref_get(v___y_1233_);
v___x_1241_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1232_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1264_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1264_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1264_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_lctx_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1262_; 
v_lctx_1246_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1240_, 1);
lean_dec(v_unused_1263_);
v___x_1248_ = v___x_1240_;
v_isShared_1249_ = v_isSharedCheck_1262_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_lctx_1246_);
lean_dec(v___x_1240_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1262_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
uint8_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1250_ = lean_unbox(v_a_1242_);
lean_dec(v_a_1242_);
v___x_1251_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1246_, v___x_1250_);
lean_dec_ref(v_lctx_1246_);
v___x_1252_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1234_);
v___x_1253_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___closed__2);
v___x_1254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1254_, 0, v_env_1239_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
lean_ctor_set(v___x_1254_, 2, v___x_1251_);
lean_ctor_set(v___x_1254_, 3, v___x_1252_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 3);
lean_ctor_set(v___x_1248_, 1, v_msg_1231_);
lean_ctor_set(v___x_1248_, 0, v___x_1254_);
v___x_1256_ = v___x_1248_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_msg_1231_);
v___x_1256_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
lean_inc(v_ref_1237_);
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v_ref_1237_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set_tag(v___x_1244_, 1);
lean_ctor_set(v___x_1244_, 0, v___x_1257_);
v___x_1259_ = v___x_1244_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v___x_1240_);
lean_dec_ref(v_env_1239_);
lean_dec_ref(v_msg_1231_);
v_a_1265_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1241_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1241_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(lean_object* v_msg_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_msg_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object* v_as_1280_, size_t v_i_1281_, size_t v_stop_1282_, lean_object* v_b_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_a_1287_; uint8_t v___x_1291_; 
v___x_1291_ = lean_usize_dec_eq(v_i_1281_, v_stop_1282_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; lean_object* v_snd_1293_; uint8_t v___x_1294_; 
v___x_1292_ = lean_array_uget_borrowed(v_as_1280_, v_i_1281_);
v_snd_1293_ = lean_ctor_get(v___x_1292_, 1);
v___x_1294_ = lean_unbox(v_snd_1293_);
if (v___x_1294_ == 0)
{
v_a_1287_ = v_b_1283_;
goto v___jp_1286_;
}
else
{
lean_object* v_fst_1295_; lean_object* v___x_1296_; 
v_fst_1295_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_fst_1295_);
v___x_1296_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_fst_1295_, v___y_1284_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1298_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v___x_1298_ = lean_array_push(v_b_1283_, v_a_1297_);
v_a_1287_ = v___x_1298_;
goto v___jp_1286_;
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref(v_b_1283_);
v_a_1299_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1296_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1296_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
else
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_b_1283_);
return v___x_1307_;
}
v___jp_1286_:
{
size_t v___x_1288_; size_t v___x_1289_; 
v___x_1288_ = ((size_t)1ULL);
v___x_1289_ = lean_usize_add(v_i_1281_, v___x_1288_);
v_i_1281_ = v___x_1289_;
v_b_1283_ = v_a_1287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object* v_as_1308_, lean_object* v_i_1309_, lean_object* v_stop_1310_, lean_object* v_b_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
size_t v_i_boxed_1314_; size_t v_stop_boxed_1315_; lean_object* v_res_1316_; 
v_i_boxed_1314_ = lean_unbox_usize(v_i_1309_);
lean_dec(v_i_1309_);
v_stop_boxed_1315_ = lean_unbox_usize(v_stop_1310_);
lean_dec(v_stop_1310_);
v_res_1316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_1308_, v_i_boxed_1314_, v_stop_boxed_1315_, v_b_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v_as_1308_);
return v_res_1316_;
}
}
static lean_object* _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17___closed__0(void){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Array_instInhabited___redArg();
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17(lean_object* v_msg_1318_){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_obj_once(&l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17___closed__0, &l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17___closed__0_once, _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17___closed__0);
v___x_1320_ = lean_panic_fn_borrowed(v___x_1319_, v_msg_1318_);
return v___x_1320_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__3(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1324_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__2));
v___x_1325_ = lean_unsigned_to_nat(11u);
v___x_1326_ = lean_unsigned_to_nat(163u);
v___x_1327_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__1));
v___x_1328_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__0));
v___x_1329_ = l_mkPanicMessageWithDecl(v___x_1328_, v___x_1327_, v___x_1326_, v___x_1325_, v___x_1324_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12(lean_object* v_a_1330_, lean_object* v_x_1331_){
_start:
{
if (lean_obj_tag(v_x_1331_) == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___closed__3);
v___x_1333_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12_spec__17(v___x_1332_);
return v___x_1333_;
}
else
{
lean_object* v_key_1334_; lean_object* v_value_1335_; lean_object* v_tail_1336_; uint8_t v___x_1337_; 
v_key_1334_ = lean_ctor_get(v_x_1331_, 0);
v_value_1335_ = lean_ctor_get(v_x_1331_, 1);
v_tail_1336_ = lean_ctor_get(v_x_1331_, 2);
v___x_1337_ = l_Lean_instBEqFVarId_beq(v_key_1334_, v_a_1330_);
if (v___x_1337_ == 0)
{
v_x_1331_ = v_tail_1336_;
goto _start;
}
else
{
lean_inc(v_value_1335_);
return v_value_1335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12___boxed(lean_object* v_a_1339_, lean_object* v_x_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12(v_a_1339_, v_x_1340_);
lean_dec(v_x_1340_);
lean_dec(v_a_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(lean_object* v_m_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_buckets_1344_; lean_object* v___x_1345_; uint64_t v___x_1346_; uint64_t v___x_1347_; uint64_t v___x_1348_; uint64_t v_fold_1349_; uint64_t v___x_1350_; uint64_t v___x_1351_; uint64_t v___x_1352_; size_t v___x_1353_; size_t v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v_buckets_1344_ = lean_ctor_get(v_m_1342_, 1);
v___x_1345_ = lean_array_get_size(v_buckets_1344_);
v___x_1346_ = l_Lean_instHashableFVarId_hash(v_a_1343_);
v___x_1347_ = 32ULL;
v___x_1348_ = lean_uint64_shift_right(v___x_1346_, v___x_1347_);
v_fold_1349_ = lean_uint64_xor(v___x_1346_, v___x_1348_);
v___x_1350_ = 16ULL;
v___x_1351_ = lean_uint64_shift_right(v_fold_1349_, v___x_1350_);
v___x_1352_ = lean_uint64_xor(v_fold_1349_, v___x_1351_);
v___x_1353_ = lean_uint64_to_usize(v___x_1352_);
v___x_1354_ = lean_usize_of_nat(v___x_1345_);
v___x_1355_ = ((size_t)1ULL);
v___x_1356_ = lean_usize_sub(v___x_1354_, v___x_1355_);
v___x_1357_ = lean_usize_land(v___x_1353_, v___x_1356_);
v___x_1358_ = lean_array_uget_borrowed(v_buckets_1344_, v___x_1357_);
v___x_1359_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__12(v_a_1343_, v___x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(lean_object* v_m_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_m_1360_, v_a_1361_);
lean_dec(v_a_1361_);
lean_dec_ref(v_m_1360_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(size_t v_sz_1363_, size_t v_i_1364_, lean_object* v_bs_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_usize_dec_lt(v_i_1364_, v_sz_1363_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v_bs_1365_);
return v___x_1372_;
}
else
{
lean_object* v_v_1373_; lean_object* v___x_1374_; lean_object* v_bs_x27_1375_; lean_object* v___x_1376_; 
v_v_1373_ = lean_array_uget(v_bs_1365_, v_i_1364_);
v___x_1374_ = lean_unsigned_to_nat(0u);
v_bs_x27_1375_ = lean_array_uset(v_bs_1365_, v_i_1364_, v___x_1374_);
v___x_1376_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_v_1373_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; size_t v___x_1378_; size_t v___x_1379_; lean_object* v___x_1380_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1378_ = ((size_t)1ULL);
v___x_1379_ = lean_usize_add(v_i_1364_, v___x_1378_);
v___x_1380_ = lean_array_uset(v_bs_x27_1375_, v_i_1364_, v_a_1377_);
v_i_1364_ = v___x_1379_;
v_bs_1365_ = v___x_1380_;
goto _start;
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec_ref(v_bs_x27_1375_);
v_a_1382_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1376_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1376_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(lean_object* v_sz_1390_, lean_object* v_i_1391_, lean_object* v_bs_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
size_t v_sz_boxed_1398_; size_t v_i_boxed_1399_; lean_object* v_res_1400_; 
v_sz_boxed_1398_ = lean_unbox_usize(v_sz_1390_);
lean_dec(v_sz_1390_);
v_i_boxed_1399_ = lean_unbox_usize(v_i_1391_);
lean_dec(v_i_1391_);
v_res_1400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_boxed_1398_, v_i_boxed_1399_, v_bs_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec(v___y_1393_);
return v_res_1400_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1403_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1));
v___x_1404_ = lean_unsigned_to_nat(12u);
v___x_1405_ = lean_unsigned_to_nat(148u);
v___x_1406_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1407_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1408_ = l_mkPanicMessageWithDecl(v___x_1407_, v___x_1406_, v___x_1405_, v___x_1404_, v___x_1403_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(lean_object* v_k_1409_, lean_object* v_decl_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v___x_1417_; lean_object* v_lctx_1418_; lean_object* v_nextIdx_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1439_; 
v___x_1417_ = lean_st_ref_take(v_a_1413_);
v_lctx_1418_ = lean_ctor_get(v___x_1417_, 0);
v_nextIdx_1419_ = lean_ctor_get(v___x_1417_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1421_ = v___x_1417_;
v_isShared_1422_ = v_isSharedCheck_1439_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_nextIdx_1419_);
lean_inc(v_lctx_1418_);
lean_dec(v___x_1417_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1439_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
uint8_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1423_ = 1;
lean_inc_ref(v_decl_1410_);
v___x_1424_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1423_, v_lctx_1418_, v_decl_1410_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1424_);
v___x_1426_ = v___x_1421_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_nextIdx_1419_);
v___x_1426_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_st_ref_put(v_a_1413_, v___x_1426_);
v___x_1428_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1409_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v_decl_1410_);
lean_ctor_set(v___x_1433_, 1, v_a_1429_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1433_);
v___x_1435_ = v___x_1431_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
lean_dec_ref(v_decl_1410_);
return v___x_1428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(lean_object* v_k_1440_, lean_object* v_fvarId_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v_subst_1450_; lean_object* v_jpParamMask_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1461_; 
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_st_ref_take(v_a_1442_);
v_subst_1450_ = lean_ctor_get(v___x_1449_, 0);
v_jpParamMask_1451_ = lean_ctor_get(v___x_1449_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1453_ = v___x_1449_;
v_isShared_1454_ = v_isSharedCheck_1461_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_jpParamMask_1451_);
lean_inc(v_subst_1450_);
lean_dec(v___x_1449_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1461_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1450_, v_fvarId_1441_, v___x_1448_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1455_);
v___x_1457_ = v___x_1453_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_jpParamMask_1451_);
v___x_1457_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_st_ref_put(v_a_1442_, v___x_1457_);
v___x_1459_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1440_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
return v___x_1459_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(lean_object* v_decl_1463_, lean_object* v_k_1464_, lean_object* v_name_1465_, lean_object* v_numParams_1466_, lean_object* v_args_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v_fvarId_1474_; lean_object* v_binderName_1475_; lean_object* v_type_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1538_; 
v_fvarId_1474_ = lean_ctor_get(v_decl_1463_, 0);
v_binderName_1475_ = lean_ctor_get(v_decl_1463_, 1);
v_type_1476_ = lean_ctor_get(v_decl_1463_, 2);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_decl_1463_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v_decl_1463_, 3);
lean_dec(v_unused_1539_);
v___x_1478_ = v_decl_1463_;
v_isShared_1479_ = v_isSharedCheck_1538_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_type_1476_);
lean_inc(v_binderName_1475_);
lean_inc(v_fvarId_1474_);
lean_dec(v_decl_1463_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1538_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1476_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1482_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1481_);
lean_dec(v_a_1481_);
v___x_1483_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1466_);
v___x_1484_ = l_Array_extract___redArg(v_args_1467_, v___x_1483_, v_numParams_1466_);
v___x_1485_ = lean_array_get_size(v_args_1467_);
v___x_1486_ = l_Array_extract___redArg(v_args_1467_, v_numParams_1466_, v___x_1485_);
v___x_1487_ = 1;
v___x_1488_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0));
lean_inc(v_binderName_1475_);
v___x_1489_ = l_Lean_Name_str___override(v_binderName_1475_, v___x_1488_);
v___x_1490_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4);
v___x_1491_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_name_1465_);
lean_ctor_set(v___x_1491_, 1, v___x_1484_);
v___x_1492_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1487_, v___x_1489_, v___x_1490_, v___x_1491_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v_fvarId_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref_known(v___x_1492_, 1);
v_fvarId_1494_ = lean_ctor_get(v_a_1493_, 0);
lean_inc(v_fvarId_1494_);
v___x_1495_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_fvarId_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1486_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 3, v___x_1495_);
lean_ctor_set(v___x_1478_, 2, v___x_1482_);
v___x_1497_ = v___x_1478_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_fvarId_1474_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_binderName_1475_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1498_; lean_object* v_lctx_1499_; lean_object* v_nextIdx_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1520_; 
v___x_1498_ = lean_st_ref_take(v_a_1470_);
v_lctx_1499_ = lean_ctor_get(v___x_1498_, 0);
v_nextIdx_1500_ = lean_ctor_get(v___x_1498_, 1);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1502_ = v___x_1498_;
v_isShared_1503_ = v_isSharedCheck_1520_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_nextIdx_1500_);
lean_inc(v_lctx_1499_);
lean_dec(v___x_1498_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1520_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
lean_inc_ref(v___x_1497_);
v___x_1504_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1487_, v_lctx_1499_, v___x_1497_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1504_);
v___x_1506_ = v___x_1502_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_nextIdx_1500_);
v___x_1506_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_st_ref_put(v_a_1470_, v___x_1506_);
v___x_1508_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1464_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1518_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1518_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1518_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1497_);
lean_ctor_set(v___x_1513_, 1, v_a_1509_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_a_1493_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1514_);
v___x_1516_ = v___x_1511_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
else
{
lean_dec_ref(v___x_1497_);
lean_dec(v_a_1493_);
return v___x_1508_;
}
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v___x_1486_);
lean_dec_ref(v___x_1482_);
lean_del_object(v___x_1478_);
lean_dec(v_binderName_1475_);
lean_dec(v_fvarId_1474_);
lean_dec_ref(v_k_1464_);
v_a_1522_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1492_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1492_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_del_object(v___x_1478_);
lean_dec(v_binderName_1475_);
lean_dec(v_fvarId_1474_);
lean_dec(v_numParams_1466_);
lean_dec(v_name_1465_);
lean_dec_ref(v_k_1464_);
v_a_1530_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1480_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1480_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(lean_object* v_decl_1540_, lean_object* v_k_1541_, lean_object* v_name_1542_, lean_object* v_args_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_fvarId_1550_; lean_object* v_binderName_1551_; lean_object* v_type_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1571_; 
v_fvarId_1550_ = lean_ctor_get(v_decl_1540_, 0);
v_binderName_1551_ = lean_ctor_get(v_decl_1540_, 1);
v_type_1552_ = lean_ctor_get(v_decl_1540_, 2);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_decl_1540_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v_decl_1540_, 3);
lean_dec(v_unused_1572_);
v___x_1554_ = v_decl_1540_;
v_isShared_1555_ = v_isSharedCheck_1571_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_type_1552_);
lean_inc(v_binderName_1551_);
lean_inc(v_fvarId_1550_);
lean_dec(v_decl_1540_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1571_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1552_, v_a_1547_, v_a_1548_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v___x_1558_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_name_1542_);
lean_ctor_set(v___x_1558_, 1, v_args_1543_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 3, v___x_1558_);
lean_ctor_set(v___x_1554_, 2, v_a_1557_);
v___x_1560_ = v___x_1554_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_fvarId_1550_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_binderName_1551_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_a_1557_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1561_; 
v___x_1561_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1541_, v___x_1560_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
return v___x_1561_;
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_del_object(v___x_1554_);
lean_dec(v_binderName_1551_);
lean_dec(v_fvarId_1550_);
lean_dec_ref(v_args_1543_);
lean_dec(v_name_1542_);
lean_dec_ref(v_k_1541_);
v_a_1563_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1556_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1556_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(lean_object* v_decl_1573_, lean_object* v_k_1574_, lean_object* v_name_1575_, lean_object* v_args_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_fvarId_1583_; lean_object* v_binderName_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1594_; 
v_fvarId_1583_ = lean_ctor_get(v_decl_1573_, 0);
v_binderName_1584_ = lean_ctor_get(v_decl_1573_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_decl_1573_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; lean_object* v_unused_1596_; 
v_unused_1595_ = lean_ctor_get(v_decl_1573_, 3);
lean_dec(v_unused_1595_);
v_unused_1596_ = lean_ctor_get(v_decl_1573_, 2);
lean_dec(v_unused_1596_);
v___x_1586_ = v_decl_1573_;
v_isShared_1587_ = v_isSharedCheck_1594_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_binderName_1584_);
lean_inc(v_fvarId_1583_);
lean_dec(v_decl_1573_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1594_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1588_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs_spec__0___redArg___closed__4);
v___x_1589_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_name_1575_);
lean_ctor_set(v___x_1589_, 1, v_args_1576_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 3, v___x_1589_);
lean_ctor_set(v___x_1586_, 2, v___x_1588_);
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_fvarId_1583_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_binderName_1584_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; 
v___x_1592_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1574_, v___x_1591_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
return v___x_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(lean_object* v_decl_1597_, lean_object* v_k_1598_, lean_object* v_name_1599_, lean_object* v_numParams_1600_, lean_object* v_args_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_numArgs_1608_; uint8_t v___x_1609_; 
v_numArgs_1608_ = lean_array_get_size(v_args_1601_);
v___x_1609_ = lean_nat_dec_lt(v_numArgs_1608_, v_numParams_1600_);
if (v___x_1609_ == 0)
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_nat_dec_eq(v_numArgs_1608_, v_numParams_1600_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
v___x_1611_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_1597_, v_k_1598_, v_name_1599_, v_numParams_1600_, v_args_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec_ref(v_args_1601_);
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; 
lean_dec(v_numParams_1600_);
v___x_1612_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1597_, v_k_1598_, v_name_1599_, v_args_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1612_;
}
}
else
{
lean_object* v___x_1613_; 
lean_dec(v_numParams_1600_);
v___x_1613_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_1597_, v_k_1598_, v_name_1599_, v_args_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1613_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1615_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3));
v___x_1616_ = lean_unsigned_to_nat(14u);
v___x_1617_ = lean_unsigned_to_nat(219u);
v___x_1618_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1619_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1620_ = l_mkPanicMessageWithDecl(v___x_1619_, v___x_1618_, v___x_1617_, v___x_1616_, v___x_1615_);
return v___x_1620_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
v___x_1628_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(lean_object* v_decl_1637_, lean_object* v_k_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v_fvarId_1653_; lean_object* v_binderName_1654_; lean_object* v_type_1655_; lean_object* v_value_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v_subst_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_2145_; 
v_fvarId_1653_ = lean_ctor_get(v_decl_1637_, 0);
v_binderName_1654_ = lean_ctor_get(v_decl_1637_, 1);
v_type_1655_ = lean_ctor_get(v_decl_1637_, 2);
v_value_1656_ = lean_ctor_get(v_decl_1637_, 3);
v___x_1657_ = lean_box(0);
v___x_1658_ = 0;
v___x_1659_ = 1;
v___x_1660_ = lean_box(0);
v___x_1661_ = lean_st_ref_get(v_a_1639_);
v_subst_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; 
v_unused_2146_ = lean_ctor_get(v___x_1661_, 1);
lean_dec(v_unused_2146_);
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_2145_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_subst_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_2145_;
goto v_resetjp_1663_;
}
v___jp_1645_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2);
v___x_1652_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1651_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
return v___x_1652_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; 
lean_inc(v_value_1656_);
v___x_1666_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v___x_1658_, v_subst_1662_, v_value_1656_, v___x_1659_);
lean_dec_ref(v_subst_1662_);
switch(lean_obj_tag(v___x_1666_))
{
case 0:
{
lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1683_; 
lean_inc(v_binderName_1654_);
lean_inc(v_fvarId_1653_);
lean_del_object(v___x_1664_);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_decl_1637_);
if (v_isSharedCheck_1683_ == 0)
{
lean_object* v_unused_1684_; lean_object* v_unused_1685_; lean_object* v_unused_1686_; lean_object* v_unused_1687_; 
v_unused_1684_ = lean_ctor_get(v_decl_1637_, 3);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_decl_1637_, 2);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_decl_1637_, 1);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_decl_1637_, 0);
lean_dec(v_unused_1687_);
v___x_1668_ = v_decl_1637_;
v_isShared_1669_ = v_isSharedCheck_1683_;
goto v_resetjp_1667_;
}
else
{
lean_dec(v_decl_1637_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1683_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v_value_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1682_; 
v_value_1670_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1672_ = v___x_1666_;
v_isShared_1673_ = v_isSharedCheck_1682_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_value_1670_);
lean_dec(v___x_1666_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1682_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1674_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_value_1670_);
if (v_isShared_1673_ == 0)
{
v___x_1676_ = v___x_1672_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_value_1670_);
v___x_1676_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1678_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 3, v___x_1676_);
lean_ctor_set(v___x_1668_, 2, v___x_1674_);
v___x_1678_ = v___x_1668_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_fvarId_1653_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_binderName_1654_);
lean_ctor_set(v_reuseFailAlloc_1680_, 2, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1680_, 3, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1679_; 
v___x_1679_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1638_, v___x_1678_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1679_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1688_; 
lean_inc(v_fvarId_1653_);
lean_del_object(v___x_1664_);
lean_dec_ref(v_decl_1637_);
v___x_1688_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1638_, v_fvarId_1653_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1688_;
}
case 2:
{
lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1808_; 
lean_inc(v_binderName_1654_);
lean_inc(v_fvarId_1653_);
lean_del_object(v___x_1664_);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_decl_1637_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; lean_object* v_unused_1810_; lean_object* v_unused_1811_; lean_object* v_unused_1812_; 
v_unused_1809_ = lean_ctor_get(v_decl_1637_, 3);
lean_dec(v_unused_1809_);
v_unused_1810_ = lean_ctor_get(v_decl_1637_, 2);
lean_dec(v_unused_1810_);
v_unused_1811_ = lean_ctor_get(v_decl_1637_, 1);
lean_dec(v_unused_1811_);
v_unused_1812_ = lean_ctor_get(v_decl_1637_, 0);
lean_dec(v_unused_1812_);
v___x_1690_ = v_decl_1637_;
v_isShared_1691_ = v_isSharedCheck_1808_;
goto v_resetjp_1689_;
}
else
{
lean_dec(v_decl_1637_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1808_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v_typeName_1692_; lean_object* v_idx_1693_; lean_object* v_struct_1694_; lean_object* v___x_1695_; 
v_typeName_1692_ = lean_ctor_get(v___x_1666_, 0);
lean_inc_n(v_typeName_1692_, 2);
v_idx_1693_ = lean_ctor_get(v___x_1666_, 1);
lean_inc(v_idx_1693_);
v_struct_1694_ = lean_ctor_get(v___x_1666_, 2);
lean_inc(v_struct_1694_);
lean_dec_ref_known(v___x_1666_, 3);
v___x_1695_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_1692_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1695_, 1);
if (lean_obj_tag(v_a_1696_) == 1)
{
lean_object* v_val_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1732_; 
lean_dec(v_typeName_1692_);
lean_del_object(v___x_1690_);
lean_dec(v_binderName_1654_);
v_val_1697_ = lean_ctor_get(v_a_1696_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_a_1696_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1699_ = v_a_1696_;
v_isShared_1700_ = v_isSharedCheck_1732_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_val_1697_);
lean_dec(v_a_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1732_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v_fieldIdx_1701_; uint8_t v___x_1702_; 
v_fieldIdx_1701_ = lean_ctor_get(v_val_1697_, 2);
lean_inc(v_fieldIdx_1701_);
lean_dec(v_val_1697_);
v___x_1702_ = lean_nat_dec_eq(v_fieldIdx_1701_, v_idx_1693_);
lean_dec(v_idx_1693_);
lean_dec(v_fieldIdx_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v_subst_1704_; lean_object* v_jpParamMask_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1715_; 
lean_del_object(v___x_1699_);
lean_dec(v_struct_1694_);
v___x_1703_ = lean_st_ref_take(v_a_1639_);
v_subst_1704_ = lean_ctor_get(v___x_1703_, 0);
v_jpParamMask_1705_ = lean_ctor_get(v___x_1703_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1707_ = v___x_1703_;
v_isShared_1708_ = v_isSharedCheck_1715_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_jpParamMask_1705_);
lean_inc(v_subst_1704_);
lean_dec(v___x_1703_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1715_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1709_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1704_, v_fvarId_1653_, v___x_1660_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1709_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_jpParamMask_1705_);
v___x_1711_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_st_ref_put(v_a_1639_, v___x_1711_);
v___x_1713_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1713_;
}
}
}
else
{
lean_object* v___x_1717_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v_struct_1694_);
v___x_1717_ = v___x_1699_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_struct_1694_);
v___x_1717_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1718_; lean_object* v_subst_1719_; lean_object* v_jpParamMask_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1730_; 
v___x_1718_ = lean_st_ref_take(v_a_1639_);
v_subst_1719_ = lean_ctor_get(v___x_1718_, 0);
v_jpParamMask_1720_ = lean_ctor_get(v___x_1718_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1722_ = v___x_1718_;
v_isShared_1723_ = v_isSharedCheck_1730_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_jpParamMask_1720_);
lean_inc(v_subst_1719_);
lean_dec(v___x_1718_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1730_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1719_, v_fvarId_1653_, v___x_1717_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1724_);
v___x_1726_ = v___x_1722_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_jpParamMask_1720_);
v___x_1726_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = lean_st_ref_put(v_a_1639_, v___x_1726_);
v___x_1728_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1728_;
}
}
}
}
}
}
else
{
lean_object* v___x_1733_; lean_object* v_subst_1734_; lean_object* v___x_1735_; 
lean_dec(v_a_1696_);
v___x_1733_ = lean_st_ref_get(v_a_1639_);
v_subst_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc_ref(v_subst_1734_);
lean_dec(v___x_1733_);
v___x_1735_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1734_, v_struct_1694_, v___x_1659_);
lean_dec_ref(v_subst_1734_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_fvarId_1736_; lean_object* v___x_1737_; lean_object* v_env_1738_; uint8_t v___x_1739_; lean_object* v___x_1740_; 
v_fvarId_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_fvarId_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v___x_1737_ = lean_st_ref_get(v_a_1643_);
v_env_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc_ref(v_env_1738_);
lean_dec(v___x_1737_);
v___x_1739_ = 0;
v___x_1740_ = l_Lean_Environment_find_x3f(v_env_1738_, v_typeName_1692_, v___x_1739_);
if (lean_obj_tag(v___x_1740_) == 1)
{
lean_object* v_val_1741_; 
v_val_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_val_1741_);
lean_dec_ref_known(v___x_1740_, 1);
if (lean_obj_tag(v_val_1741_) == 5)
{
lean_object* v_val_1742_; lean_object* v_ctors_1743_; 
v_val_1742_ = lean_ctor_get(v_val_1741_, 0);
lean_inc_ref(v_val_1742_);
lean_dec_ref_known(v_val_1741_, 1);
v_ctors_1743_ = lean_ctor_get(v_val_1742_, 4);
lean_inc(v_ctors_1743_);
lean_dec_ref(v_val_1742_);
if (lean_obj_tag(v_ctors_1743_) == 1)
{
lean_object* v_tail_1744_; 
v_tail_1744_ = lean_ctor_get(v_ctors_1743_, 1);
if (lean_obj_tag(v_tail_1744_) == 0)
{
lean_object* v_head_1745_; lean_object* v___x_1746_; 
v_head_1745_ = lean_ctor_get(v_ctors_1743_, 0);
lean_inc(v_head_1745_);
lean_dec_ref_known(v_ctors_1743_, 2);
v___x_1746_ = l_Lean_Compiler_LCNF_getCtorLayout(v_head_1745_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v_ctorInfo_1748_; lean_object* v_fieldInfo_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v_ctorInfo_1748_ = lean_ctor_get(v_a_1747_, 0);
lean_inc_ref(v_ctorInfo_1748_);
v_fieldInfo_1749_ = lean_ctor_get(v_a_1747_, 1);
lean_inc_ref(v_fieldInfo_1749_);
lean_dec(v_a_1747_);
v___x_1750_ = lean_array_get(v___x_1657_, v_fieldInfo_1749_, v_idx_1693_);
lean_dec(v_idx_1693_);
lean_dec_ref(v_fieldInfo_1749_);
v___x_1751_ = l_Lean_Compiler_LCNF_CtorFieldInfo_spillDepth(v___x_1750_);
lean_inc(v_fvarId_1736_);
v___x_1752_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs(v_fvarId_1736_, v___x_1751_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
lean_dec(v___x_1751_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; lean_object* v_fst_1755_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_fvarId_1736_, v_a_1753_, v_ctorInfo_1748_, v___x_1750_);
lean_dec_ref(v_ctorInfo_1748_);
v_fst_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_fst_1755_);
if (lean_obj_tag(v_fst_1755_) == 1)
{
lean_object* v___x_1756_; 
lean_dec_ref(v___x_1754_);
lean_dec(v_a_1753_);
lean_del_object(v___x_1690_);
lean_dec(v_binderName_1654_);
v___x_1756_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1638_, v_fvarId_1653_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1756_;
}
else
{
lean_object* v_snd_1757_; lean_object* v___x_1759_; 
v_snd_1757_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_snd_1757_);
lean_dec_ref(v___x_1754_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 3, v_fst_1755_);
lean_ctor_set(v___x_1690_, 2, v_snd_1757_);
v___x_1759_ = v___x_1690_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_fvarId_1653_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_binderName_1654_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_snd_1757_);
lean_ctor_set(v_reuseFailAlloc_1770_, 3, v_fst_1755_);
v___x_1759_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1760_; 
v___x_1760_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1638_, v___x_1759_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1769_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1769_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1769_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1765_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls(v_a_1753_, v_a_1761_);
lean_dec(v_a_1753_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1765_);
v___x_1767_ = v___x_1763_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
else
{
lean_dec(v_a_1753_);
return v___x_1760_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v___x_1750_);
lean_dec_ref(v_ctorInfo_1748_);
lean_dec(v_fvarId_1736_);
lean_del_object(v___x_1690_);
lean_dec(v_binderName_1654_);
lean_dec(v_fvarId_1653_);
lean_dec_ref(v_k_1638_);
v_a_1771_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1752_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1752_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v_fvarId_1736_);
lean_dec(v_idx_1693_);
lean_del_object(v___x_1690_);
lean_dec(v_binderName_1654_);
lean_dec(v_fvarId_1653_);
lean_dec_ref(v_k_1638_);
v_a_1779_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1746_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1746_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1743_, 2);
lean_dec(v_fvarId_1736_);
lean_dec(v_idx_1693_);
lean_del_object(v___x_1690_);
lean_dec(v_binderName_1654_);
lean_dec(v_fvarId_1653_);
lean_dec_ref(v_k_1638_);
v___y_1646_ = v_a_1639_;
v___y_1647_ = v_a_1640_;
v___y_1648_ = v_a_1641_;
v___y_1649_ = v_a_1642_;
v___y_1650_ = v_a_1643_;
goto v___jp_1645_;
}
}
else
{
lean_dec(v_ctors_1743_);
lean_dec(v_fvarId_1736_);
lean_dec(v_idx_1693_);
lean_del_object(v___x_1690_);
lean_dec(v_binderName_1654_);
lean_dec(v_fvarId_1653_);
lean_dec_ref(v_k_1638_);
v___y_1646_ = v_a_1639_;
v___y_1647_ = v_a_1640_;
v___y_1648_ = v_a_1641_;
v___y_1649_ = v_a_1642_;
v___y_1650_ = v_a_1643_;
goto v___jp_1645_;
}
}
else
{
lean_dec(v_val_1741_);
lean_dec(v_fvarId_1736_);
lean_dec(v_idx_1693_);
lean_del_object(v___x_1690_);
lean_dec(v_binderName_1654_);
lean_dec(v_fvarId_1653_);
lean_dec_ref(v_k_1638_);
v___y_1646_ = v_a_1639_;
v___y_1647_ = v_a_1640_;
v___y_1648_ = v_a_1641_;
v___y_1649_ = v_a_1642_;
v___y_1650_ = v_a_1643_;
goto v___jp_1645_;
}
}
else
{
lean_dec(v___x_1740_);
lean_dec(v_fvarId_1736_);
lean_dec(v_idx_1693_);
lean_del_object(v___x_1690_);
lean_dec(v_binderName_1654_);
lean_dec(v_fvarId_1653_);
lean_dec_ref(v_k_1638_);
v___y_1646_ = v_a_1639_;
v___y_1647_ = v_a_1640_;
v___y_1648_ = v_a_1641_;
v___y_1649_ = v_a_1642_;
v___y_1650_ = v_a_1643_;
goto v___jp_1645_;
}
}
else
{
lean_object* v___x_1787_; lean_object* v_subst_1788_; lean_object* v_jpParamMask_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_idx_1693_);
lean_dec(v_typeName_1692_);
lean_del_object(v___x_1690_);
lean_dec(v_binderName_1654_);
v___x_1787_ = lean_st_ref_take(v_a_1639_);
v_subst_1788_ = lean_ctor_get(v___x_1787_, 0);
v_jpParamMask_1789_ = lean_ctor_get(v___x_1787_, 1);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1791_ = v___x_1787_;
v_isShared_1792_ = v_isSharedCheck_1799_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_jpParamMask_1789_);
lean_inc(v_subst_1788_);
lean_dec(v___x_1787_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1799_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1793_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1788_, v_fvarId_1653_, v___x_1660_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v___x_1793_);
v___x_1795_ = v___x_1791_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_jpParamMask_1789_);
v___x_1795_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = lean_st_ref_put(v_a_1639_, v___x_1795_);
v___x_1797_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1797_;
}
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec(v_struct_1694_);
lean_dec(v_idx_1693_);
lean_dec(v_typeName_1692_);
lean_del_object(v___x_1690_);
lean_dec(v_binderName_1654_);
lean_dec(v_fvarId_1653_);
lean_dec_ref(v_k_1638_);
v_a_1800_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1695_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1695_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
case 3:
{
lean_object* v_declName_1813_; lean_object* v_args_1814_; size_t v_sz_1815_; size_t v___x_1816_; lean_object* v___x_1817_; 
v_declName_1813_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_declName_1813_);
v_args_1814_ = lean_ctor_get(v___x_1666_, 2);
lean_inc_ref_n(v_args_1814_, 2);
lean_dec_ref_known(v___x_1666_, 3);
v_sz_1815_ = lean_array_size(v_args_1814_);
v___x_1816_ = ((size_t)0ULL);
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_sz_1815_, v___x_1816_, v_args_1814_, v_a_1639_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1819_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref_known(v___x_1817_, 1);
lean_inc(v_declName_1813_);
v___x_1819_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1813_, v_a_1643_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___x_1819_, 1);
if (lean_obj_tag(v_a_1820_) == 1)
{
lean_object* v_val_1821_; lean_object* v_params_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec_ref(v_args_1814_);
lean_del_object(v___x_1664_);
v_val_1821_ = lean_ctor_get(v_a_1820_, 0);
lean_inc(v_val_1821_);
lean_dec_ref_known(v_a_1820_, 1);
v_params_1822_ = lean_ctor_get(v_val_1821_, 3);
lean_inc_ref(v_params_1822_);
lean_dec(v_val_1821_);
v___x_1823_ = lean_array_get_size(v_params_1822_);
lean_dec_ref(v_params_1822_);
v___x_1824_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1637_, v_k_1638_, v_declName_1813_, v___x_1823_, v_a_1818_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; 
lean_dec(v_a_1820_);
lean_inc(v_declName_1813_);
v___x_1825_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1813_, v_a_1643_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1825_, 1);
if (lean_obj_tag(v_a_1826_) == 1)
{
lean_object* v_val_1827_; lean_object* v_toSignature_1828_; lean_object* v_params_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref(v_args_1814_);
lean_del_object(v___x_1664_);
v_val_1827_ = lean_ctor_get(v_a_1826_, 0);
lean_inc(v_val_1827_);
lean_dec_ref_known(v_a_1826_, 1);
v_toSignature_1828_ = lean_ctor_get(v_val_1827_, 0);
lean_inc_ref(v_toSignature_1828_);
lean_dec(v_val_1827_);
v_params_1829_ = lean_ctor_get(v_toSignature_1828_, 3);
lean_inc_ref(v_params_1829_);
lean_dec_ref(v_toSignature_1828_);
v___x_1830_ = lean_array_get_size(v_params_1829_);
lean_dec_ref(v_params_1829_);
v___x_1831_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1637_, v_k_1638_, v_declName_1813_, v___x_1830_, v_a_1818_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1831_;
}
else
{
lean_object* v___x_1832_; lean_object* v_env_1833_; uint8_t v___x_1834_; lean_object* v___x_1835_; 
lean_dec(v_a_1826_);
v___x_1832_ = lean_st_ref_get(v_a_1643_);
v_env_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc_ref(v_env_1833_);
lean_dec(v___x_1832_);
v___x_1834_ = 0;
lean_inc(v_declName_1813_);
v___x_1835_ = l_Lean_Environment_find_x3f(v_env_1833_, v_declName_1813_, v___x_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_dec(v_a_1818_);
lean_dec_ref(v_args_1814_);
lean_dec(v_declName_1813_);
lean_del_object(v___x_1664_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v___x_1836_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4);
v___x_1837_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1836_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1837_;
}
else
{
lean_object* v_val_1838_; 
v_val_1838_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_val_1838_);
lean_dec_ref_known(v___x_1835_, 1);
switch(lean_obj_tag(v_val_1838_))
{
case 0:
{
lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_a_1818_);
lean_dec_ref(v_args_1814_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_val_1838_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v_val_1838_, 0);
lean_dec(v_unused_1855_);
v___x_1840_ = v_val_1838_;
v_isShared_1841_ = v_isSharedCheck_1854_;
goto v_resetjp_1839_;
}
else
{
lean_dec(v_val_1838_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1854_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1842_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1843_ = l_Lean_Name_toString(v_declName_1813_, v___x_1659_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set_tag(v___x_1840_, 3);
lean_ctor_set(v___x_1840_, 0, v___x_1843_);
v___x_1845_ = v___x_1840_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1847_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 5);
lean_ctor_set(v___x_1664_, 1, v___x_1845_);
lean_ctor_set(v___x_1664_, 0, v___x_1842_);
v___x_1847_ = v___x_1664_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1848_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = l_Lean_MessageData_ofFormat(v___x_1849_);
v___x_1851_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1850_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1851_;
}
}
}
}
case 2:
{
lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1871_; 
lean_dec(v_a_1818_);
lean_dec_ref(v_args_1814_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_val_1838_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; 
v_unused_1872_ = lean_ctor_get(v_val_1838_, 0);
lean_dec(v_unused_1872_);
v___x_1857_ = v_val_1838_;
v_isShared_1858_ = v_isSharedCheck_1871_;
goto v_resetjp_1856_;
}
else
{
lean_dec(v_val_1838_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1871_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1859_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1860_ = l_Lean_Name_toString(v_declName_1813_, v___x_1659_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set_tag(v___x_1857_, 3);
lean_ctor_set(v___x_1857_, 0, v___x_1860_);
v___x_1862_ = v___x_1857_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1864_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 5);
lean_ctor_set(v___x_1664_, 1, v___x_1862_);
lean_ctor_set(v___x_1664_, 0, v___x_1859_);
v___x_1864_ = v___x_1664_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1865_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = l_Lean_MessageData_ofFormat(v___x_1866_);
v___x_1868_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1867_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1868_;
}
}
}
}
case 4:
{
lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v_a_1818_);
lean_dec_ref(v_args_1814_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_val_1838_);
if (v_isSharedCheck_1888_ == 0)
{
lean_object* v_unused_1889_; 
v_unused_1889_ = lean_ctor_get(v_val_1838_, 0);
lean_dec(v_unused_1889_);
v___x_1874_ = v_val_1838_;
v_isShared_1875_ = v_isSharedCheck_1888_;
goto v_resetjp_1873_;
}
else
{
lean_dec(v_val_1838_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1888_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1876_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1877_ = l_Lean_Name_toString(v_declName_1813_, v___x_1659_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 3);
lean_ctor_set(v___x_1874_, 0, v___x_1877_);
v___x_1879_ = v___x_1874_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1881_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 5);
lean_ctor_set(v___x_1664_, 1, v___x_1879_);
lean_ctor_set(v___x_1664_, 0, v___x_1876_);
v___x_1881_ = v___x_1664_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1882_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1881_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = l_Lean_MessageData_ofFormat(v___x_1883_);
v___x_1885_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1884_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1885_;
}
}
}
}
case 5:
{
lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_a_1818_);
lean_dec_ref(v_args_1814_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_val_1838_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; 
v_unused_1906_ = lean_ctor_get(v_val_1838_, 0);
lean_dec(v_unused_1906_);
v___x_1891_ = v_val_1838_;
v_isShared_1892_ = v_isSharedCheck_1905_;
goto v_resetjp_1890_;
}
else
{
lean_dec(v_val_1838_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1905_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1893_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1894_ = l_Lean_Name_toString(v_declName_1813_, v___x_1659_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set_tag(v___x_1891_, 3);
lean_ctor_set(v___x_1891_, 0, v___x_1894_);
v___x_1896_ = v___x_1891_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1898_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 5);
lean_ctor_set(v___x_1664_, 1, v___x_1896_);
lean_ctor_set(v___x_1664_, 0, v___x_1893_);
v___x_1898_ = v___x_1664_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1899_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = l_Lean_MessageData_ofFormat(v___x_1900_);
v___x_1902_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1901_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1902_;
}
}
}
}
case 6:
{
lean_object* v_val_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_2058_; 
lean_del_object(v___x_1664_);
v_val_1907_ = lean_ctor_get(v_val_1838_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_val_1838_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_1909_ = v_val_1838_;
v_isShared_1910_ = v_isSharedCheck_2058_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_val_1907_);
lean_dec(v_val_1838_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_2058_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_induct_1911_; lean_object* v_cidx_1912_; lean_object* v_numParams_1913_; lean_object* v___x_1914_; 
v_induct_1911_ = lean_ctor_get(v_val_1907_, 1);
lean_inc_n(v_induct_1911_, 2);
v_cidx_1912_ = lean_ctor_get(v_val_1907_, 2);
lean_inc(v_cidx_1912_);
v_numParams_1913_ = lean_ctor_get(v_val_1907_, 3);
lean_inc(v_numParams_1913_);
lean_dec_ref(v_val_1907_);
v___x_1914_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_induct_1911_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
if (lean_obj_tag(v_a_1915_) == 1)
{
lean_object* v_val_1916_; lean_object* v_numParams_1917_; lean_object* v_fieldIdx_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v_subst_1922_; lean_object* v_jpParamMask_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1933_; 
lean_inc(v_fvarId_1653_);
lean_dec(v_numParams_1913_);
lean_dec(v_cidx_1912_);
lean_dec(v_induct_1911_);
lean_del_object(v___x_1909_);
lean_dec(v_a_1818_);
lean_dec(v_declName_1813_);
lean_dec_ref(v_decl_1637_);
v_val_1916_ = lean_ctor_get(v_a_1915_, 0);
lean_inc(v_val_1916_);
lean_dec_ref_known(v_a_1915_, 1);
v_numParams_1917_ = lean_ctor_get(v_val_1916_, 1);
lean_inc(v_numParams_1917_);
v_fieldIdx_1918_ = lean_ctor_get(v_val_1916_, 2);
lean_inc(v_fieldIdx_1918_);
lean_dec(v_val_1916_);
v___x_1919_ = lean_nat_add(v_numParams_1917_, v_fieldIdx_1918_);
lean_dec(v_fieldIdx_1918_);
lean_dec(v_numParams_1917_);
v___x_1920_ = lean_array_get(v___x_1660_, v_args_1814_, v___x_1919_);
lean_dec(v___x_1919_);
lean_dec_ref(v_args_1814_);
v___x_1921_ = lean_st_ref_take(v_a_1639_);
v_subst_1922_ = lean_ctor_get(v___x_1921_, 0);
v_jpParamMask_1923_ = lean_ctor_get(v___x_1921_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1925_ = v___x_1921_;
v_isShared_1926_ = v_isSharedCheck_1933_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_jpParamMask_1923_);
lean_inc(v_subst_1922_);
lean_dec(v___x_1921_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1933_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1927_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1922_, v_fvarId_1653_, v___x_1920_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1927_);
v___x_1929_ = v___x_1925_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_jpParamMask_1923_);
v___x_1929_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = lean_st_ref_put(v_a_1639_, v___x_1929_);
v___x_1931_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1931_;
}
}
}
else
{
lean_object* v___x_1934_; 
lean_dec(v_a_1915_);
lean_dec_ref(v_args_1814_);
v___x_1934_ = l_Lean_Compiler_LCNF_nameToImpureType(v_induct_1911_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; uint8_t v___x_1936_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1936_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; 
lean_dec(v_a_1935_);
lean_dec(v_cidx_1912_);
lean_del_object(v___x_1909_);
lean_inc(v_declName_1813_);
v___x_1937_ = l_Lean_Compiler_LCNF_getCtorLayout(v_declName_1813_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_2017_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_2017_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_2017_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v_ctorInfo_1947_; lean_object* v_fieldInfo_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_2016_; 
v_ctorInfo_1947_ = lean_ctor_get(v_a_1938_, 0);
v_fieldInfo_1948_ = lean_ctor_get(v_a_1938_, 1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_a_1938_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1950_ = v_a_1938_;
v_isShared_1951_ = v_isSharedCheck_2016_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_fieldInfo_1948_);
lean_inc(v_ctorInfo_1947_);
lean_dec(v_a_1938_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_2016_;
goto v_resetjp_1949_;
}
v___jp_1942_:
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1943_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1943_);
v___x_1945_ = v___x_1940_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1952_ = lean_array_get_size(v_a_1818_);
v___x_1953_ = l_Array_extract___redArg(v_a_1818_, v_numParams_1913_, v___x_1952_);
lean_dec(v_a_1818_);
v___x_1954_ = lean_array_get_size(v___x_1953_);
v___x_1955_ = lean_array_get_size(v_fieldInfo_1948_);
v___x_1956_ = lean_nat_dec_eq(v___x_1954_, v___x_1955_);
if (v___x_1956_ == 0)
{
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1950_);
lean_dec_ref(v_fieldInfo_1948_);
lean_dec_ref(v_ctorInfo_1947_);
lean_dec(v_declName_1813_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
goto v___jp_1942_;
}
else
{
if (v___x_1936_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_del_object(v___x_1940_);
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_1959_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___redArg(v___x_1955_, v_fieldInfo_1948_, v___x_1953_, v___x_1957_, v___x_1958_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1961_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1959_, 1);
v___x_1961_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_mkSpillObjs(v_declName_1813_, v_a_1960_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v_fst_1963_; lean_object* v_snd_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1999_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref_known(v___x_1961_, 1);
v_fst_1963_ = lean_ctor_get(v_a_1962_, 0);
v_snd_1964_ = lean_ctor_get(v_a_1962_, 1);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_a_1962_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1966_ = v_a_1962_;
v_isShared_1967_ = v_isSharedCheck_1999_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_snd_1964_);
lean_inc(v_fst_1963_);
lean_dec(v_a_1962_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1999_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
uint8_t v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1968_ = 1;
v___x_1969_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_ctorInfo_1947_);
lean_inc_ref(v_ctorInfo_1947_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set_tag(v___x_1966_, 5);
lean_ctor_set(v___x_1966_, 0, v_ctorInfo_1947_);
v___x_1971_ = v___x_1966_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_ctorInfo_1947_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_snd_1964_);
v___x_1971_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_lctx_1974_; lean_object* v_nextIdx_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1997_; 
lean_inc(v_binderName_1654_);
lean_inc(v_fvarId_1653_);
v___x_1972_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1972_, 0, v_fvarId_1653_);
lean_ctor_set(v___x_1972_, 1, v_binderName_1654_);
lean_ctor_set(v___x_1972_, 2, v___x_1969_);
lean_ctor_set(v___x_1972_, 3, v___x_1971_);
v___x_1973_ = lean_st_ref_take(v_a_1641_);
v_lctx_1974_ = lean_ctor_get(v___x_1973_, 0);
v_nextIdx_1975_ = lean_ctor_get(v___x_1973_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1977_ = v___x_1973_;
v_isShared_1978_ = v_isSharedCheck_1997_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_nextIdx_1975_);
lean_inc(v_lctx_1974_);
lean_dec(v___x_1973_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1997_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1981_; 
lean_inc_ref(v___x_1972_);
v___x_1979_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1968_, v_lctx_1974_, v___x_1972_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1979_);
v___x_1981_ = v___x_1977_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_nextIdx_1975_);
v___x_1981_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_st_ref_put(v_a_1641_, v___x_1981_);
v___x_1983_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_1637_, v_k_1638_, v_ctorInfo_1947_, v_fieldInfo_1948_, v___x_1953_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
lean_dec_ref(v___x_1953_);
lean_dec_ref(v_fieldInfo_1948_);
lean_dec_ref(v_ctorInfo_1947_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1995_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_1995_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1995_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v_a_1984_);
lean_ctor_set(v___x_1950_, 0, v___x_1972_);
v___x_1989_ = v___x_1950_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1990_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls(v_fst_1963_, v___x_1989_);
lean_dec(v_fst_1963_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1990_);
v___x_1992_ = v___x_1986_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1972_, 4);
lean_dec(v_fst_1963_);
lean_del_object(v___x_1950_);
return v___x_1983_;
}
}
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1950_);
lean_dec_ref(v_fieldInfo_1948_);
lean_dec_ref(v_ctorInfo_1947_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v_a_2000_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1961_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1961_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1950_);
lean_dec_ref(v_fieldInfo_1948_);
lean_dec_ref(v_ctorInfo_1947_);
lean_dec(v_declName_1813_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v_a_2008_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1959_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1959_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1950_);
lean_dec_ref(v_fieldInfo_1948_);
lean_dec_ref(v_ctorInfo_1947_);
lean_dec(v_declName_1813_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
goto v___jp_1942_;
}
}
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_numParams_1913_);
lean_dec(v_a_1818_);
lean_dec(v_declName_1813_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v_a_2018_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_1937_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_1937_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2037_; 
lean_inc(v_binderName_1654_);
lean_inc(v_fvarId_1653_);
lean_dec(v_numParams_1913_);
lean_dec(v_a_1818_);
lean_dec(v_declName_1813_);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_decl_1637_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; lean_object* v_unused_2039_; lean_object* v_unused_2040_; lean_object* v_unused_2041_; 
v_unused_2038_ = lean_ctor_get(v_decl_1637_, 3);
lean_dec(v_unused_2038_);
v_unused_2039_ = lean_ctor_get(v_decl_1637_, 2);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_decl_1637_, 1);
lean_dec(v_unused_2040_);
v_unused_2041_ = lean_ctor_get(v_decl_1637_, 0);
lean_dec(v_unused_2041_);
v___x_2027_ = v_decl_1637_;
v_isShared_2028_ = v_isSharedCheck_2037_;
goto v_resetjp_2026_;
}
else
{
lean_dec(v_decl_1637_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2037_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2029_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_1935_, v_cidx_1912_);
lean_dec(v_cidx_1912_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set_tag(v___x_1909_, 0);
lean_ctor_set(v___x_1909_, 0, v___x_2029_);
v___x_2031_ = v___x_1909_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 3, v___x_2031_);
lean_ctor_set(v___x_2027_, 2, v_a_1935_);
v___x_2033_ = v___x_2027_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_fvarId_1653_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_binderName_1654_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_a_1935_);
lean_ctor_set(v_reuseFailAlloc_2035_, 3, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; 
v___x_2034_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1638_, v___x_2033_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_2034_;
}
}
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v_numParams_1913_);
lean_dec(v_cidx_1912_);
lean_del_object(v___x_1909_);
lean_dec(v_a_1818_);
lean_dec(v_declName_1813_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v_a_2042_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_1934_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_1934_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_numParams_1913_);
lean_dec(v_cidx_1912_);
lean_dec(v_induct_1911_);
lean_del_object(v___x_1909_);
lean_dec(v_a_1818_);
lean_dec_ref(v_args_1814_);
lean_dec(v_declName_1813_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v_a_2050_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_1914_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_1914_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
case 7:
{
lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v_a_1818_);
lean_dec_ref(v_args_1814_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_val_1838_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v_val_1838_, 0);
lean_dec(v_unused_2075_);
v___x_2060_ = v_val_1838_;
v_isShared_2061_ = v_isSharedCheck_2074_;
goto v_resetjp_2059_;
}
else
{
lean_dec(v_val_1838_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2074_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2062_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11));
v___x_2063_ = l_Lean_Name_toString(v_declName_1813_, v___x_1659_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set_tag(v___x_2060_, 3);
lean_ctor_set(v___x_2060_, 0, v___x_2063_);
v___x_2065_ = v___x_2060_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2067_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 5);
lean_ctor_set(v___x_1664_, 1, v___x_2065_);
lean_ctor_set(v___x_1664_, 0, v___x_2062_);
v___x_2067_ = v___x_1664_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2068_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13));
v___x_2069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = l_Lean_MessageData_ofFormat(v___x_2069_);
v___x_2071_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_2070_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_2071_;
}
}
}
}
default: 
{
lean_object* v___x_2076_; 
lean_dec(v_val_1838_);
lean_dec_ref(v_args_1814_);
lean_del_object(v___x_1664_);
v___x_2076_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1637_, v_k_1638_, v_declName_1813_, v_a_1818_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_2076_;
}
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec(v_a_1818_);
lean_dec_ref(v_args_1814_);
lean_dec(v_declName_1813_);
lean_del_object(v___x_1664_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v_a_2077_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_1825_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_1825_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec(v_a_1818_);
lean_dec_ref(v_args_1814_);
lean_dec(v_declName_1813_);
lean_del_object(v___x_1664_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v_a_2085_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_1819_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_1819_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec_ref(v_args_1814_);
lean_dec(v_declName_1813_);
lean_del_object(v___x_1664_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_decl_1637_);
v_a_2093_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_1817_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_1817_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
default: 
{
lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2140_; 
lean_inc_ref(v_type_1655_);
lean_inc(v_binderName_1654_);
lean_inc(v_fvarId_1653_);
lean_del_object(v___x_1664_);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_decl_1637_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; lean_object* v_unused_2142_; lean_object* v_unused_2143_; lean_object* v_unused_2144_; 
v_unused_2141_ = lean_ctor_get(v_decl_1637_, 3);
lean_dec(v_unused_2141_);
v_unused_2142_ = lean_ctor_get(v_decl_1637_, 2);
lean_dec(v_unused_2142_);
v_unused_2143_ = lean_ctor_get(v_decl_1637_, 1);
lean_dec(v_unused_2143_);
v_unused_2144_ = lean_ctor_get(v_decl_1637_, 0);
lean_dec(v_unused_2144_);
v___x_2102_ = v_decl_1637_;
v_isShared_2103_ = v_isSharedCheck_2140_;
goto v_resetjp_2101_;
}
else
{
lean_dec(v_decl_1637_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2140_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v_fvarId_2104_; lean_object* v_args_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2139_; 
v_fvarId_2104_ = lean_ctor_get(v___x_1666_, 0);
v_args_2105_ = lean_ctor_get(v___x_1666_, 1);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2107_ = v___x_1666_;
v_isShared_2108_ = v_isSharedCheck_2139_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_args_2105_);
lean_inc(v_fvarId_2104_);
lean_dec(v___x_1666_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2139_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
size_t v_sz_2109_; size_t v___x_2110_; lean_object* v___x_2111_; 
v_sz_2109_ = lean_array_size(v_args_2105_);
v___x_2110_ = ((size_t)0ULL);
v___x_2111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_sz_2109_, v___x_2110_, v_args_2105_, v_a_1639_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2113_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1655_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2115_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_2114_);
lean_dec(v_a_2114_);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 1, v_a_2112_);
v___x_2117_ = v___x_2107_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_fvarId_2104_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2119_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 3, v___x_2117_);
lean_ctor_set(v___x_2102_, 2, v___x_2115_);
v___x_2119_ = v___x_2102_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_fvarId_1653_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_binderName_1654_);
lean_ctor_set(v_reuseFailAlloc_2121_, 2, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2121_, 3, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; 
v___x_2120_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1638_, v___x_2119_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_2120_;
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v_a_2112_);
lean_del_object(v___x_2107_);
lean_dec(v_fvarId_2104_);
lean_del_object(v___x_2102_);
lean_dec(v_binderName_1654_);
lean_dec(v_fvarId_1653_);
lean_dec_ref(v_k_1638_);
v_a_2123_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2113_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2113_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_del_object(v___x_2107_);
lean_dec(v_fvarId_2104_);
lean_del_object(v___x_2102_);
lean_dec_ref(v_type_1655_);
lean_dec(v_binderName_1654_);
lean_dec(v_fvarId_1653_);
lean_dec_ref(v_k_1638_);
v_a_2131_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2111_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2111_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
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
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2149_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1));
v___x_2150_ = lean_unsigned_to_nat(15u);
v___x_2151_ = lean_unsigned_to_nat(306u);
v___x_2152_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2153_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2154_ = l_mkPanicMessageWithDecl(v___x_2153_, v___x_2152_, v___x_2151_, v___x_2150_, v___x_2149_);
return v___x_2154_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5(void){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_2157_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2159_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6));
v___x_2160_ = lean_unsigned_to_nat(6u);
v___x_2161_ = lean_unsigned_to_nat(285u);
v___x_2162_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2163_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2164_ = l_mkPanicMessageWithDecl(v___x_2163_, v___x_2162_, v___x_2161_, v___x_2160_, v___x_2159_);
return v___x_2164_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2166_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8));
v___x_2167_ = lean_unsigned_to_nat(6u);
v___x_2168_ = lean_unsigned_to_nat(287u);
v___x_2169_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2170_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2171_ = l_mkPanicMessageWithDecl(v___x_2170_, v___x_2169_, v___x_2168_, v___x_2167_, v___x_2166_);
return v___x_2171_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2173_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10));
v___x_2174_ = lean_unsigned_to_nat(6u);
v___x_2175_ = lean_unsigned_to_nat(288u);
v___x_2176_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2177_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2178_ = l_mkPanicMessageWithDecl(v___x_2177_, v___x_2176_, v___x_2175_, v___x_2174_, v___x_2173_);
return v___x_2178_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2180_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12));
v___x_2181_ = lean_unsigned_to_nat(45u);
v___x_2182_ = lean_unsigned_to_nat(286u);
v___x_2183_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2184_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2185_ = l_mkPanicMessageWithDecl(v___x_2184_, v___x_2183_, v___x_2182_, v___x_2181_, v___x_2180_);
return v___x_2185_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2188_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1));
v___x_2189_ = lean_unsigned_to_nat(18u);
v___x_2190_ = lean_unsigned_to_nat(328u);
v___x_2191_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0));
v___x_2192_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2193_ = l_mkPanicMessageWithDecl(v___x_2192_, v___x_2191_, v___x_2190_, v___x_2189_, v___x_2188_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object* v_discr_2194_, lean_object* v_k_2195_, lean_object* v_ctorInfo_2196_, lean_object* v_spills_2197_, lean_object* v_params_2198_, lean_object* v_fields_2199_, lean_object* v_i_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = lean_array_get_size(v_params_2198_);
v___x_2216_ = lean_nat_dec_lt(v_i_2200_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; uint8_t v___x_2218_; 
lean_dec(v_discr_2194_);
v___x_2217_ = lean_array_get_size(v_fields_2199_);
v___x_2218_ = lean_nat_dec_lt(v_i_2200_, v___x_2217_);
lean_dec(v_i_2200_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; 
v___x_2219_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2195_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
return v___x_2219_;
}
else
{
lean_dec_ref(v_k_2195_);
v___y_2208_ = v_a_2201_;
v___y_2209_ = v_a_2202_;
v___y_2210_ = v_a_2203_;
v___y_2211_ = v_a_2204_;
v___y_2212_ = v_a_2205_;
goto v___jp_2207_;
}
}
else
{
lean_object* v___x_2220_; uint8_t v___x_2221_; 
v___x_2220_ = lean_array_get_size(v_fields_2199_);
v___x_2221_ = lean_nat_dec_lt(v_i_2200_, v___x_2220_);
if (v___x_2221_ == 0)
{
lean_dec(v_i_2200_);
lean_dec_ref(v_k_2195_);
lean_dec(v_discr_2194_);
v___y_2208_ = v_a_2201_;
v___y_2209_ = v_a_2202_;
v___y_2210_ = v_a_2203_;
v___y_2211_ = v_a_2204_;
v___y_2212_ = v_a_2205_;
goto v___jp_2207_;
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v_fst_2224_; lean_object* v_snd_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2277_; 
v___x_2222_ = lean_array_fget_borrowed(v_fields_2199_, v_i_2200_);
lean_inc(v___x_2222_);
lean_inc(v_discr_2194_);
v___x_2223_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_discr_2194_, v_spills_2197_, v_ctorInfo_2196_, v___x_2222_);
v_fst_2224_ = lean_ctor_get(v___x_2223_, 0);
v_snd_2225_ = lean_ctor_get(v___x_2223_, 1);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2227_ = v___x_2223_;
v_isShared_2228_ = v_isSharedCheck_2277_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_snd_2225_);
lean_inc(v_fst_2224_);
lean_dec(v___x_2223_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2277_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_array_fget_borrowed(v_params_2198_, v_i_2200_);
if (lean_obj_tag(v_fst_2224_) == 1)
{
lean_object* v_fvarId_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v_subst_2233_; lean_object* v_jpParamMask_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2246_; 
lean_del_object(v___x_2227_);
lean_dec(v_snd_2225_);
v_fvarId_2230_ = lean_ctor_get(v___x_2229_, 0);
v___x_2231_ = lean_box(0);
v___x_2232_ = lean_st_ref_take(v_a_2201_);
v_subst_2233_ = lean_ctor_get(v___x_2232_, 0);
v_jpParamMask_2234_ = lean_ctor_get(v___x_2232_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2236_ = v___x_2232_;
v_isShared_2237_ = v_isSharedCheck_2246_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_jpParamMask_2234_);
lean_inc(v_subst_2233_);
lean_dec(v___x_2232_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2246_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2238_; lean_object* v___x_2240_; 
lean_inc(v_fvarId_2230_);
v___x_2238_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_2233_, v_fvarId_2230_, v___x_2231_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v___x_2238_);
v___x_2240_ = v___x_2236_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2238_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_jpParamMask_2234_);
v___x_2240_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = lean_st_ref_put(v_a_2201_, v___x_2240_);
v___x_2242_ = lean_unsigned_to_nat(1u);
v___x_2243_ = lean_nat_add(v_i_2200_, v___x_2242_);
lean_dec(v_i_2200_);
v_i_2200_ = v___x_2243_;
goto _start;
}
}
}
else
{
lean_object* v_fvarId_2247_; lean_object* v_binderName_2248_; uint8_t v___x_2249_; lean_object* v_decl_2250_; lean_object* v___x_2251_; lean_object* v_lctx_2252_; lean_object* v_nextIdx_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2276_; 
v_fvarId_2247_ = lean_ctor_get(v___x_2229_, 0);
v_binderName_2248_ = lean_ctor_get(v___x_2229_, 1);
v___x_2249_ = 1;
lean_inc(v_binderName_2248_);
lean_inc(v_fvarId_2247_);
v_decl_2250_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_2250_, 0, v_fvarId_2247_);
lean_ctor_set(v_decl_2250_, 1, v_binderName_2248_);
lean_ctor_set(v_decl_2250_, 2, v_snd_2225_);
lean_ctor_set(v_decl_2250_, 3, v_fst_2224_);
v___x_2251_ = lean_st_ref_take(v_a_2203_);
v_lctx_2252_ = lean_ctor_get(v___x_2251_, 0);
v_nextIdx_2253_ = lean_ctor_get(v___x_2251_, 1);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2255_ = v___x_2251_;
v_isShared_2256_ = v_isSharedCheck_2276_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_nextIdx_2253_);
lean_inc(v_lctx_2252_);
lean_dec(v___x_2251_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2276_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2259_; 
lean_inc_ref(v_decl_2250_);
v___x_2257_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2249_, v_lctx_2252_, v_decl_2250_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2257_);
v___x_2259_ = v___x_2255_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_nextIdx_2253_);
v___x_2259_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2260_ = lean_st_ref_put(v_a_2203_, v___x_2259_);
v___x_2261_ = lean_unsigned_to_nat(1u);
v___x_2262_ = lean_nat_add(v_i_2200_, v___x_2261_);
lean_dec(v_i_2200_);
v___x_2263_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2194_, v_k_2195_, v_ctorInfo_2196_, v_spills_2197_, v_params_2198_, v_fields_2199_, v___x_2262_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2274_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2266_ = v___x_2263_;
v_isShared_2267_ = v_isSharedCheck_2274_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2263_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2274_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 1, v_a_2264_);
lean_ctor_set(v___x_2227_, 0, v_decl_2250_);
v___x_2269_ = v___x_2227_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_decl_2250_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2271_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2269_);
v___x_2271_ = v___x_2266_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
else
{
lean_dec_ref_known(v_decl_2250_, 4);
lean_del_object(v___x_2227_);
return v___x_2263_;
}
}
}
}
}
}
}
v___jp_2207_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2);
v___x_2214_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2213_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
return v___x_2214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(lean_object* v_discr_2278_, lean_object* v_alt_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
if (lean_obj_tag(v_alt_2279_) == 0)
{
lean_object* v_ctorName_2286_; lean_object* v_params_2287_; lean_object* v_code_2288_; lean_object* v___x_2289_; 
v_ctorName_2286_ = lean_ctor_get(v_alt_2279_, 0);
lean_inc(v_ctorName_2286_);
v_params_2287_ = lean_ctor_get(v_alt_2279_, 1);
lean_inc_ref(v_params_2287_);
v_code_2288_ = lean_ctor_get(v_alt_2279_, 2);
lean_inc_ref(v_code_2288_);
lean_dec_ref_known(v_alt_2279_, 3);
v___x_2289_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_2286_, v_a_2283_, v_a_2284_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v_ctorInfo_2291_; lean_object* v_fieldInfo_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2339_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v_ctorInfo_2291_ = lean_ctor_get(v_a_2290_, 0);
v_fieldInfo_2292_ = lean_ctor_get(v_a_2290_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_a_2290_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2294_ = v_a_2290_;
v_isShared_2295_ = v_isSharedCheck_2339_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_fieldInfo_2292_);
lean_inc(v_ctorInfo_2291_);
lean_dec(v_a_2290_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2339_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v___y_2298_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2296_ = lean_unsigned_to_nat(0u);
v___x_2330_ = lean_array_get_size(v_fieldInfo_2292_);
v___x_2331_ = lean_nat_dec_lt(v___x_2296_, v___x_2330_);
if (v___x_2331_ == 0)
{
v___y_2298_ = v___x_2296_;
goto v___jp_2297_;
}
else
{
uint8_t v___x_2332_; 
v___x_2332_ = lean_nat_dec_le(v___x_2330_, v___x_2330_);
if (v___x_2332_ == 0)
{
if (v___x_2331_ == 0)
{
v___y_2298_ = v___x_2296_;
goto v___jp_2297_;
}
else
{
size_t v___x_2333_; size_t v___x_2334_; lean_object* v___x_2335_; 
v___x_2333_ = ((size_t)0ULL);
v___x_2334_ = lean_usize_of_nat(v___x_2330_);
v___x_2335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_spec__10(v_fieldInfo_2292_, v___x_2333_, v___x_2334_, v___x_2296_);
v___y_2298_ = v___x_2335_;
goto v___jp_2297_;
}
}
else
{
size_t v___x_2336_; size_t v___x_2337_; lean_object* v___x_2338_; 
v___x_2336_ = ((size_t)0ULL);
v___x_2337_ = lean_usize_of_nat(v___x_2330_);
v___x_2338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_spec__10(v_fieldInfo_2292_, v___x_2336_, v___x_2337_, v___x_2296_);
v___y_2298_ = v___x_2338_;
goto v___jp_2297_;
}
}
v___jp_2297_:
{
lean_object* v___x_2299_; 
lean_inc(v_discr_2278_);
v___x_2299_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerSpillObjs(v_discr_2278_, v___y_2298_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
lean_dec(v___y_2298_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2278_, v_code_2288_, v_ctorInfo_2291_, v_a_2300_, v_params_2287_, v_fieldInfo_2292_, v___x_2296_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
lean_dec_ref(v_fieldInfo_2292_);
lean_dec_ref(v_params_2287_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2313_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2313_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2313_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2306_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_attachLetDecls(v_a_2300_, v_a_2302_);
lean_dec(v_a_2300_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set_tag(v___x_2294_, 1);
lean_ctor_set(v___x_2294_, 1, v___x_2306_);
v___x_2308_ = v___x_2294_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_ctorInfo_2291_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2308_);
v___x_2310_ = v___x_2304_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v_a_2300_);
lean_del_object(v___x_2294_);
lean_dec_ref(v_ctorInfo_2291_);
v_a_2314_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2301_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2301_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_del_object(v___x_2294_);
lean_dec_ref(v_fieldInfo_2292_);
lean_dec_ref(v_ctorInfo_2291_);
lean_dec_ref(v_code_2288_);
lean_dec_ref(v_params_2287_);
lean_dec(v_discr_2278_);
v_a_2322_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2299_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2299_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v_code_2288_);
lean_dec_ref(v_params_2287_);
lean_dec(v_discr_2278_);
v_a_2340_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2289_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2289_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
else
{
lean_object* v_code_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_discr_2278_);
v_code_2348_ = lean_ctor_get(v_alt_2279_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_alt_2279_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2350_ = v_alt_2279_;
v_isShared_2351_ = v_isSharedCheck_2372_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_code_2348_);
lean_dec(v_alt_2279_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2372_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; 
v___x_2352_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_2348_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2363_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2363_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2363_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v_a_2353_);
v___x_2358_ = v___x_2350_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2360_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2358_);
v___x_2360_ = v___x_2355_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_del_object(v___x_2350_);
v_a_2364_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2352_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2352_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(lean_object* v_fvarId_2373_, size_t v_sz_2374_, size_t v_i_2375_, lean_object* v_bs_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
uint8_t v___x_2383_; 
v___x_2383_ = lean_usize_dec_lt(v_i_2375_, v_sz_2374_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; 
lean_dec(v_fvarId_2373_);
v___x_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2384_, 0, v_bs_2376_);
return v___x_2384_;
}
else
{
lean_object* v_v_2385_; lean_object* v___x_2386_; lean_object* v_bs_x27_2387_; lean_object* v___x_2388_; 
v_v_2385_ = lean_array_uget(v_bs_2376_, v_i_2375_);
v___x_2386_ = lean_unsigned_to_nat(0u);
v_bs_x27_2387_ = lean_array_uset(v_bs_2376_, v_i_2375_, v___x_2386_);
lean_inc(v_fvarId_2373_);
v___x_2388_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_fvarId_2373_, v_v_2385_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; size_t v___x_2390_; size_t v___x_2391_; lean_object* v___x_2392_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2390_ = ((size_t)1ULL);
v___x_2391_ = lean_usize_add(v_i_2375_, v___x_2390_);
v___x_2392_ = lean_array_uset(v_bs_x27_2387_, v_i_2375_, v_a_2389_);
v_i_2375_ = v___x_2391_;
v_bs_2376_ = v___x_2392_;
goto _start;
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec_ref(v_bs_x27_2387_);
lean_dec(v_fvarId_2373_);
v_a_2394_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2388_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2388_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(lean_object* v_c_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
switch(lean_obj_tag(v_c_2402_))
{
case 0:
{
lean_object* v_decl_2409_; lean_object* v_k_2410_; lean_object* v___x_2411_; 
v_decl_2409_ = lean_ctor_get(v_c_2402_, 0);
lean_inc_ref(v_decl_2409_);
v_k_2410_ = lean_ctor_get(v_c_2402_, 1);
lean_inc_ref(v_k_2410_);
lean_dec_ref_known(v_c_2402_, 2);
v___x_2411_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2409_, v_k_2410_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2411_;
}
case 1:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec_ref_known(v_c_2402_, 2);
v___x_2412_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2);
v___x_2413_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2412_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2413_;
}
case 2:
{
lean_object* v_decl_2414_; lean_object* v_k_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2507_; 
v_decl_2414_ = lean_ctor_get(v_c_2402_, 0);
v_k_2415_ = lean_ctor_get(v_c_2402_, 1);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_c_2402_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2417_ = v_c_2402_;
v_isShared_2418_ = v_isSharedCheck_2507_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_k_2415_);
lean_inc(v_decl_2414_);
lean_dec(v_c_2402_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2507_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v_fvarId_2419_; lean_object* v_binderName_2420_; lean_object* v_params_2421_; lean_object* v_type_2422_; lean_object* v_value_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2506_; 
v_fvarId_2419_ = lean_ctor_get(v_decl_2414_, 0);
v_binderName_2420_ = lean_ctor_get(v_decl_2414_, 1);
v_params_2421_ = lean_ctor_get(v_decl_2414_, 2);
v_type_2422_ = lean_ctor_get(v_decl_2414_, 3);
v_value_2423_ = lean_ctor_get(v_decl_2414_, 4);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_decl_2414_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2425_ = v_decl_2414_;
v_isShared_2426_ = v_isSharedCheck_2506_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_value_2423_);
lean_inc(v_type_2422_);
lean_inc(v_params_2421_);
lean_inc(v_binderName_2420_);
lean_inc(v_fvarId_2419_);
lean_dec(v_decl_2414_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2506_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
size_t v_sz_2427_; size_t v___x_2428_; lean_object* v___x_2429_; 
v_sz_2427_ = lean_array_size(v_params_2421_);
v___x_2428_ = ((size_t)0ULL);
v___x_2429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2427_, v___x_2428_, v_params_2421_, v_a_2403_, v_a_2405_, v_a_2406_, v_a_2407_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; size_t v_sz_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v_subst_2434_; lean_object* v_jpParamMask_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2497_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc_n(v_a_2430_, 2);
lean_dec_ref_known(v___x_2429_, 1);
v_sz_2431_ = lean_array_size(v_a_2430_);
v___x_2432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_2431_, v___x_2428_, v_a_2430_);
v___x_2433_ = lean_st_ref_take(v_a_2403_);
v_subst_2434_ = lean_ctor_get(v___x_2433_, 0);
v_jpParamMask_2435_ = lean_ctor_get(v___x_2433_, 1);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2437_ = v___x_2433_;
v_isShared_2438_ = v_isSharedCheck_2497_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_jpParamMask_2435_);
lean_inc(v_subst_2434_);
lean_dec(v___x_2433_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2497_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2441_; 
lean_inc_ref(v___x_2432_);
lean_inc(v_fvarId_2419_);
v___x_2439_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_jpParamMask_2435_, v_fvarId_2419_, v___x_2432_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 1, v___x_2439_);
v___x_2441_ = v___x_2437_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_subst_2434_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2439_);
v___x_2441_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; lean_object* v___y_2444_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2442_ = lean_st_ref_put(v_a_2403_, v___x_2441_);
v___x_2486_ = lean_unsigned_to_nat(0u);
v___x_2487_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3));
v___x_2488_ = l_Array_zip___redArg(v_a_2430_, v___x_2432_);
lean_dec_ref(v___x_2432_);
v___x_2489_ = lean_array_get_size(v___x_2488_);
v___x_2490_ = lean_nat_dec_lt(v___x_2486_, v___x_2489_);
if (v___x_2490_ == 0)
{
lean_dec_ref(v___x_2488_);
v___y_2444_ = v___x_2487_;
goto v___jp_2443_;
}
else
{
uint8_t v___x_2491_; 
v___x_2491_ = lean_nat_dec_le(v___x_2489_, v___x_2489_);
if (v___x_2491_ == 0)
{
if (v___x_2490_ == 0)
{
lean_dec_ref(v___x_2488_);
v___y_2444_ = v___x_2487_;
goto v___jp_2443_;
}
else
{
size_t v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = lean_usize_of_nat(v___x_2489_);
v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2488_, v___x_2428_, v___x_2492_, v___x_2487_);
lean_dec_ref(v___x_2488_);
v___y_2444_ = v___x_2493_;
goto v___jp_2443_;
}
}
else
{
size_t v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = lean_usize_of_nat(v___x_2489_);
v___x_2495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2488_, v___x_2428_, v___x_2494_, v___x_2487_);
lean_dec_ref(v___x_2488_);
v___y_2444_ = v___x_2495_;
goto v___jp_2443_;
}
}
v___jp_2443_:
{
lean_object* v___x_2445_; 
v___x_2445_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_value_2423_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2447_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2445_, 1);
v___x_2447_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2415_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
lean_dec_ref_known(v___x_2447_, 1);
v___x_2449_ = lean_array_get_size(v_a_2430_);
lean_dec(v_a_2430_);
v___x_2450_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2422_, v___x_2449_, v_a_2406_, v_a_2407_);
lean_dec_ref(v_type_2422_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2477_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2477_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2477_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
uint8_t v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = 1;
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 4, v_a_2446_);
lean_ctor_set(v___x_2425_, 3, v_a_2451_);
lean_ctor_set(v___x_2425_, 2, v___y_2444_);
v___x_2457_ = v___x_2425_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_fvarId_2419_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_binderName_2420_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v___y_2444_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v_a_2451_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v_a_2446_);
v___x_2457_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v_lctx_2459_; lean_object* v_nextIdx_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2475_; 
v___x_2458_ = lean_st_ref_take(v_a_2405_);
v_lctx_2459_ = lean_ctor_get(v___x_2458_, 0);
v_nextIdx_2460_ = lean_ctor_get(v___x_2458_, 1);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2462_ = v___x_2458_;
v_isShared_2463_ = v_isSharedCheck_2475_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_nextIdx_2460_);
lean_inc(v_lctx_2459_);
lean_dec(v___x_2458_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2475_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2466_; 
lean_inc_ref(v___x_2457_);
v___x_2464_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2455_, v_lctx_2459_, v___x_2457_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2464_);
v___x_2466_ = v___x_2462_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_nextIdx_2460_);
v___x_2466_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = lean_st_ref_put(v_a_2405_, v___x_2466_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 1, v_a_2448_);
lean_ctor_set(v___x_2417_, 0, v___x_2457_);
v___x_2469_ = v___x_2417_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_a_2448_);
v___x_2469_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2471_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2469_);
v___x_2471_ = v___x_2453_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_dec_ref(v___y_2444_);
lean_del_object(v___x_2425_);
lean_dec(v_binderName_2420_);
lean_dec(v_fvarId_2419_);
lean_del_object(v___x_2417_);
v_a_2478_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2450_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2450_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_dec(v_a_2446_);
lean_dec_ref(v___y_2444_);
lean_dec(v_a_2430_);
lean_del_object(v___x_2425_);
lean_dec_ref(v_type_2422_);
lean_dec(v_binderName_2420_);
lean_dec(v_fvarId_2419_);
lean_del_object(v___x_2417_);
return v___x_2447_;
}
}
else
{
lean_dec_ref(v___y_2444_);
lean_dec(v_a_2430_);
lean_del_object(v___x_2425_);
lean_dec_ref(v_type_2422_);
lean_dec(v_binderName_2420_);
lean_dec(v_fvarId_2419_);
lean_del_object(v___x_2417_);
lean_dec_ref(v_k_2415_);
return v___x_2445_;
}
}
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_del_object(v___x_2425_);
lean_dec_ref(v_value_2423_);
lean_dec_ref(v_type_2422_);
lean_dec(v_binderName_2420_);
lean_dec(v_fvarId_2419_);
lean_del_object(v___x_2417_);
lean_dec_ref(v_k_2415_);
v_a_2498_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2429_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2429_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2508_; lean_object* v_args_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2545_; 
v_fvarId_2508_ = lean_ctor_get(v_c_2402_, 0);
v_args_2509_ = lean_ctor_get(v_c_2402_, 1);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_c_2402_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2511_ = v_c_2402_;
v_isShared_2512_ = v_isSharedCheck_2545_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_args_2509_);
lean_inc(v_fvarId_2508_);
lean_dec(v_c_2402_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2545_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v_a_2514_; lean_object* v___y_2520_; lean_object* v___x_2530_; lean_object* v_jpParamMask_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2530_ = lean_st_ref_get(v_a_2403_);
v_jpParamMask_2531_ = lean_ctor_get(v___x_2530_, 1);
lean_inc_ref(v_jpParamMask_2531_);
lean_dec(v___x_2530_);
v___x_2532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_jpParamMask_2531_, v_fvarId_2508_);
lean_dec_ref(v_jpParamMask_2531_);
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2534_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_2535_ = l_Array_zip___redArg(v_args_2509_, v___x_2532_);
lean_dec_ref(v___x_2532_);
lean_dec_ref(v_args_2509_);
v___x_2536_ = lean_array_get_size(v___x_2535_);
v___x_2537_ = lean_nat_dec_lt(v___x_2533_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_dec_ref(v___x_2535_);
v_a_2514_ = v___x_2534_;
goto v___jp_2513_;
}
else
{
uint8_t v___x_2538_; 
v___x_2538_ = lean_nat_dec_le(v___x_2536_, v___x_2536_);
if (v___x_2538_ == 0)
{
if (v___x_2537_ == 0)
{
lean_dec_ref(v___x_2535_);
v_a_2514_ = v___x_2534_;
goto v___jp_2513_;
}
else
{
size_t v___x_2539_; size_t v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = ((size_t)0ULL);
v___x_2540_ = lean_usize_of_nat(v___x_2536_);
v___x_2541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2535_, v___x_2539_, v___x_2540_, v___x_2534_, v_a_2403_);
lean_dec_ref(v___x_2535_);
v___y_2520_ = v___x_2541_;
goto v___jp_2519_;
}
}
else
{
size_t v___x_2542_; size_t v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = ((size_t)0ULL);
v___x_2543_ = lean_usize_of_nat(v___x_2536_);
v___x_2544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2535_, v___x_2542_, v___x_2543_, v___x_2534_, v_a_2403_);
lean_dec_ref(v___x_2535_);
v___y_2520_ = v___x_2544_;
goto v___jp_2519_;
}
}
v___jp_2513_:
{
lean_object* v___x_2516_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 1, v_a_2514_);
v___x_2516_ = v___x_2511_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_fvarId_2508_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_a_2514_);
v___x_2516_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; 
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
return v___x_2517_;
}
}
v___jp_2519_:
{
if (lean_obj_tag(v___y_2520_) == 0)
{
lean_object* v_a_2521_; 
v_a_2521_ = lean_ctor_get(v___y_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___y_2520_, 1);
v_a_2514_ = v_a_2521_;
goto v___jp_2513_;
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_del_object(v___x_2511_);
lean_dec(v_fvarId_2508_);
v_a_2522_ = lean_ctor_get(v___y_2520_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___y_2520_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___y_2520_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___y_2520_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
}
case 4:
{
lean_object* v_cases_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2656_; 
v_cases_2546_ = lean_ctor_get(v_c_2402_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_c_2402_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2548_ = v_c_2402_;
v_isShared_2549_ = v_isSharedCheck_2656_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_cases_2546_);
lean_dec(v_c_2402_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2656_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v_typeName_2550_; lean_object* v_resultType_2551_; lean_object* v_discr_2552_; lean_object* v_alts_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2655_; 
v_typeName_2550_ = lean_ctor_get(v_cases_2546_, 0);
v_resultType_2551_ = lean_ctor_get(v_cases_2546_, 1);
v_discr_2552_ = lean_ctor_get(v_cases_2546_, 2);
v_alts_2553_ = lean_ctor_get(v_cases_2546_, 3);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_cases_2546_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2555_ = v_cases_2546_;
v_isShared_2556_ = v_isSharedCheck_2655_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_alts_2553_);
lean_inc(v_discr_2552_);
lean_inc(v_resultType_2551_);
lean_inc(v_typeName_2550_);
lean_dec(v_cases_2546_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2655_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5);
lean_inc(v_typeName_2550_);
v___x_2558_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_2550_, v_a_2406_, v_a_2407_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
if (lean_obj_tag(v_a_2559_) == 1)
{
lean_object* v_val_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; 
lean_del_object(v___x_2555_);
lean_dec_ref(v_resultType_2551_);
lean_dec(v_typeName_2550_);
lean_del_object(v___x_2548_);
v_val_2560_ = lean_ctor_get(v_a_2559_, 0);
lean_inc(v_val_2560_);
lean_dec_ref_known(v_a_2559_, 1);
v___x_2561_ = lean_array_get_size(v_alts_2553_);
v___x_2562_ = lean_unsigned_to_nat(1u);
v___x_2563_ = lean_nat_dec_eq(v___x_2561_, v___x_2562_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec(v_val_2560_);
lean_dec_ref(v_alts_2553_);
lean_dec(v_discr_2552_);
v___x_2564_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7);
v___x_2565_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2564_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2565_;
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = lean_unsigned_to_nat(0u);
v___x_2567_ = lean_array_get(v___x_2557_, v_alts_2553_, v___x_2566_);
lean_dec_ref(v_alts_2553_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_ctorName_2568_; lean_object* v_params_2569_; lean_object* v_code_2570_; lean_object* v_ctorName_2571_; lean_object* v_fieldIdx_2572_; uint8_t v___x_2573_; 
v_ctorName_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_ctorName_2568_);
v_params_2569_ = lean_ctor_get(v___x_2567_, 1);
lean_inc_ref(v_params_2569_);
v_code_2570_ = lean_ctor_get(v___x_2567_, 2);
lean_inc_ref(v_code_2570_);
lean_dec_ref_known(v___x_2567_, 3);
v_ctorName_2571_ = lean_ctor_get(v_val_2560_, 0);
lean_inc(v_ctorName_2571_);
v_fieldIdx_2572_ = lean_ctor_get(v_val_2560_, 2);
lean_inc(v_fieldIdx_2572_);
lean_dec(v_val_2560_);
v___x_2573_ = lean_name_eq(v_ctorName_2568_, v_ctorName_2571_);
lean_dec(v_ctorName_2571_);
lean_dec(v_ctorName_2568_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_dec(v_fieldIdx_2572_);
lean_dec_ref(v_code_2570_);
lean_dec_ref(v_params_2569_);
lean_dec(v_discr_2552_);
v___x_2574_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9);
v___x_2575_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2574_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2575_;
}
else
{
lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = lean_array_get_size(v_params_2569_);
v___x_2577_ = lean_nat_dec_lt(v_fieldIdx_2572_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_dec(v_fieldIdx_2572_);
lean_dec_ref(v_code_2570_);
lean_dec_ref(v_params_2569_);
lean_dec(v_discr_2552_);
v___x_2578_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11);
v___x_2579_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2578_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2579_;
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = lean_box(0);
v___x_2581_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v___x_2576_, v_params_2569_, v_fieldIdx_2572_, v_discr_2552_, v___x_2566_, v___x_2580_, v_a_2403_);
lean_dec(v_fieldIdx_2572_);
lean_dec_ref(v_params_2569_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_dec_ref_known(v___x_2581_, 1);
v_c_2402_ = v_code_2570_;
goto _start;
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_dec_ref(v_code_2570_);
v_a_2583_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2581_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2581_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec(v___x_2567_);
lean_dec(v_val_2560_);
lean_dec(v_discr_2552_);
v___x_2591_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13);
v___x_2592_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2591_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2592_;
}
}
}
else
{
uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v_subst_2595_; lean_object* v___x_2596_; 
lean_dec(v_a_2559_);
v___x_2593_ = 1;
v___x_2594_ = lean_st_ref_get(v_a_2403_);
v_subst_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc_ref(v_subst_2595_);
lean_dec(v___x_2594_);
v___x_2596_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2595_, v_discr_2552_, v___x_2593_);
lean_dec_ref(v_subst_2595_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_fvarId_2597_; lean_object* v___x_2598_; 
v_fvarId_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_fvarId_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v___x_2598_ = l_Lean_Compiler_LCNF_toImpureType(v_resultType_2551_, v_a_2406_, v_a_2407_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; size_t v_sz_2600_; size_t v___x_2601_; lean_object* v___x_2602_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2598_, 1);
v_sz_2600_ = lean_array_size(v_alts_2553_);
v___x_2601_ = ((size_t)0ULL);
lean_inc(v_fvarId_2597_);
v___x_2602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2597_, v_sz_2600_, v___x_2601_, v_alts_2553_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2604_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___x_2602_, 1);
v___x_2604_ = l_Lean_Compiler_LCNF_nameToImpureType(v_typeName_2550_, v_a_2406_, v_a_2407_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2620_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2607_ = v___x_2604_;
v_isShared_2608_ = v_isSharedCheck_2620_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2620_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2609_ = l_Lean_Expr_getAppFn(v_a_2605_);
lean_dec(v_a_2605_);
v___x_2610_ = l_Lean_Expr_constName_x21(v___x_2609_);
lean_dec_ref(v___x_2609_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 3, v_a_2603_);
lean_ctor_set(v___x_2555_, 2, v_fvarId_2597_);
lean_ctor_set(v___x_2555_, 1, v_a_2599_);
lean_ctor_set(v___x_2555_, 0, v___x_2610_);
v___x_2612_ = v___x_2555_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_a_2599_);
lean_ctor_set(v_reuseFailAlloc_2619_, 2, v_fvarId_2597_);
lean_ctor_set(v_reuseFailAlloc_2619_, 3, v_a_2603_);
v___x_2612_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2614_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2612_);
v___x_2614_ = v___x_2548_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2616_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2614_);
v___x_2616_ = v___x_2607_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_a_2603_);
lean_dec(v_a_2599_);
lean_dec(v_fvarId_2597_);
lean_del_object(v___x_2555_);
lean_del_object(v___x_2548_);
v_a_2621_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2604_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2604_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v_a_2599_);
lean_dec(v_fvarId_2597_);
lean_del_object(v___x_2555_);
lean_dec(v_typeName_2550_);
lean_del_object(v___x_2548_);
v_a_2629_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2602_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2602_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v_fvarId_2597_);
lean_del_object(v___x_2555_);
lean_dec_ref(v_alts_2553_);
lean_dec(v_typeName_2550_);
lean_del_object(v___x_2548_);
v_a_2637_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2598_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2598_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
uint8_t v___x_2645_; lean_object* v___x_2646_; 
lean_del_object(v___x_2555_);
lean_dec_ref(v_alts_2553_);
lean_dec_ref(v_resultType_2551_);
lean_dec(v_typeName_2550_);
lean_del_object(v___x_2548_);
v___x_2645_ = 1;
v___x_2646_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2645_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2646_;
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_del_object(v___x_2555_);
lean_dec_ref(v_alts_2553_);
lean_dec(v_discr_2552_);
lean_dec_ref(v_resultType_2551_);
lean_dec(v_typeName_2550_);
lean_del_object(v___x_2548_);
v_a_2647_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2558_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2558_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2678_; 
v_fvarId_2657_ = lean_ctor_get(v_c_2402_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_c_2402_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2659_ = v_c_2402_;
v_isShared_2660_ = v_isSharedCheck_2678_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_fvarId_2657_);
lean_dec(v_c_2402_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2678_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
uint8_t v___x_2661_; lean_object* v___x_2662_; lean_object* v_subst_2663_; lean_object* v___x_2664_; 
v___x_2661_ = 1;
v___x_2662_ = lean_st_ref_get(v_a_2403_);
v_subst_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc_ref(v_subst_2663_);
lean_dec(v___x_2662_);
v___x_2664_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2663_, v_fvarId_2657_, v___x_2661_);
lean_dec_ref(v_subst_2663_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_fvarId_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2675_; 
v_fvarId_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2675_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_fvarId_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2675_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v_fvarId_2665_);
v___x_2670_ = v___x_2659_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_fvarId_2665_);
v___x_2670_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2672_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2670_);
v___x_2672_ = v___x_2667_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
uint8_t v___x_2676_; lean_object* v___x_2677_; 
lean_del_object(v___x_2659_);
v___x_2676_ = 1;
v___x_2677_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2676_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2677_;
}
}
}
default: 
{
lean_object* v_type_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2703_; 
v_type_2679_ = lean_ctor_get(v_c_2402_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_c_2402_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2681_ = v_c_2402_;
v_isShared_2682_ = v_isSharedCheck_2703_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_type_2679_);
lean_dec(v_c_2402_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2703_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_Compiler_LCNF_toImpureType(v_type_2679_, v_a_2406_, v_a_2407_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2694_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2694_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2694_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v_a_2684_);
v___x_2689_ = v___x_2681_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2691_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2689_);
v___x_2691_ = v___x_2686_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_del_object(v___x_2681_);
v_a_2695_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2683_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2683_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(lean_object* v_decl_2704_, lean_object* v_k_2705_, lean_object* v_ctorInfo_2706_, lean_object* v_fields_2707_, lean_object* v_irArgs_2708_, lean_object* v_i_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2716_; uint8_t v___x_2717_; 
v___x_2716_ = lean_array_get_size(v_irArgs_2708_);
v___x_2717_ = lean_nat_dec_lt(v_i_2709_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; 
lean_dec(v_i_2709_);
lean_dec_ref(v_decl_2704_);
v___x_2718_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2705_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
return v___x_2718_;
}
else
{
lean_object* v___x_2719_; 
v___x_2719_ = lean_array_fget_borrowed(v_irArgs_2708_, v_i_2709_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = lean_unsigned_to_nat(1u);
v___x_2721_ = lean_nat_add(v_i_2709_, v___x_2720_);
lean_dec(v_i_2709_);
v_i_2709_ = v___x_2721_;
goto _start;
}
else
{
lean_object* v_fvarId_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_fvarId_2723_ = lean_ctor_get(v___x_2719_, 0);
v___x_2724_ = lean_box(0);
v___x_2725_ = lean_array_get_borrowed(v___x_2724_, v_fields_2707_, v_i_2709_);
switch(lean_obj_tag(v___x_2725_))
{
case 2:
{
lean_object* v_i_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v_i_2726_ = lean_ctor_get(v___x_2725_, 0);
v___x_2727_ = lean_unsigned_to_nat(1u);
v___x_2728_ = lean_nat_add(v_i_2709_, v___x_2727_);
lean_dec(v_i_2709_);
lean_inc_ref(v_decl_2704_);
v___x_2729_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2704_, v_k_2705_, v_ctorInfo_2706_, v_fields_2707_, v_irArgs_2708_, v___x_2728_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2748_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2732_ = v___x_2729_;
v_isShared_2733_ = v_isSharedCheck_2748_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2748_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v_fvarId_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2744_; 
v_fvarId_2734_ = lean_ctor_get(v_decl_2704_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_decl_2704_);
if (v_isSharedCheck_2744_ == 0)
{
lean_object* v_unused_2745_; lean_object* v_unused_2746_; lean_object* v_unused_2747_; 
v_unused_2745_ = lean_ctor_get(v_decl_2704_, 3);
lean_dec(v_unused_2745_);
v_unused_2746_ = lean_ctor_get(v_decl_2704_, 2);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v_decl_2704_, 1);
lean_dec(v_unused_2747_);
v___x_2736_ = v_decl_2704_;
v_isShared_2737_ = v_isSharedCheck_2744_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_fvarId_2734_);
lean_dec(v_decl_2704_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2744_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
lean_inc(v_fvarId_2723_);
lean_inc(v_i_2726_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set_tag(v___x_2736_, 8);
lean_ctor_set(v___x_2736_, 3, v_a_2730_);
lean_ctor_set(v___x_2736_, 2, v_fvarId_2723_);
lean_ctor_set(v___x_2736_, 1, v_i_2726_);
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_fvarId_2734_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_i_2726_);
lean_ctor_set(v_reuseFailAlloc_2743_, 2, v_fvarId_2723_);
lean_ctor_set(v_reuseFailAlloc_2743_, 3, v_a_2730_);
v___x_2739_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_object* v___x_2741_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2739_);
v___x_2741_ = v___x_2732_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_2704_);
return v___x_2729_;
}
}
case 3:
{
lean_object* v_offset_2749_; lean_object* v_type_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v_offset_2749_ = lean_ctor_get(v___x_2725_, 1);
v_type_2750_ = lean_ctor_get(v___x_2725_, 2);
v___x_2751_ = lean_unsigned_to_nat(1u);
v___x_2752_ = lean_nat_add(v_i_2709_, v___x_2751_);
lean_dec(v_i_2709_);
lean_inc_ref(v_decl_2704_);
v___x_2753_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2704_, v_k_2705_, v_ctorInfo_2706_, v_fields_2707_, v_irArgs_2708_, v___x_2752_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2766_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2766_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2766_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v_fvarId_2758_; lean_object* v_size_2759_; lean_object* v_usize_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; 
v_fvarId_2758_ = lean_ctor_get(v_decl_2704_, 0);
lean_inc(v_fvarId_2758_);
lean_dec_ref(v_decl_2704_);
v_size_2759_ = lean_ctor_get(v_ctorInfo_2706_, 2);
v_usize_2760_ = lean_ctor_get(v_ctorInfo_2706_, 3);
v___x_2761_ = lean_nat_add(v_size_2759_, v_usize_2760_);
lean_inc_ref(v_type_2750_);
lean_inc(v_fvarId_2723_);
lean_inc(v_offset_2749_);
v___x_2762_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_2762_, 0, v_fvarId_2758_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
lean_ctor_set(v___x_2762_, 2, v_offset_2749_);
lean_ctor_set(v___x_2762_, 3, v_fvarId_2723_);
lean_ctor_set(v___x_2762_, 4, v_type_2750_);
lean_ctor_set(v___x_2762_, 5, v_a_2754_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v___x_2762_);
v___x_2764_ = v___x_2756_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
else
{
lean_dec_ref(v_decl_2704_);
return v___x_2753_;
}
}
default: 
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_unsigned_to_nat(1u);
v___x_2768_ = lean_nat_add(v_i_2709_, v___x_2767_);
lean_dec(v_i_2709_);
v_i_2709_ = v___x_2768_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(lean_object* v_decl_2770_, lean_object* v_k_2771_, lean_object* v_ctorInfo_2772_, lean_object* v_fields_2773_, lean_object* v_irArgs_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_unsigned_to_nat(0u);
v___x_2782_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2770_, v_k_2771_, v_ctorInfo_2772_, v_fields_2773_, v_irArgs_2774_, v___x_2781_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(lean_object* v_decl_2783_, lean_object* v_k_2784_, lean_object* v_ctorInfo_2785_, lean_object* v_fields_2786_, lean_object* v_irArgs_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_2783_, v_k_2784_, v_ctorInfo_2785_, v_fields_2786_, v_irArgs_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
lean_dec(v_a_2790_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2788_);
lean_dec_ref(v_irArgs_2787_);
lean_dec_ref(v_fields_2786_);
lean_dec_ref(v_ctorInfo_2785_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(lean_object* v_decl_2795_, lean_object* v_k_2796_, lean_object* v_name_2797_, lean_object* v_args_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_2795_, v_k_2796_, v_name_2797_, v_args_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
lean_dec(v_a_2799_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(lean_object* v_decl_2806_, lean_object* v_k_2807_, lean_object* v_name_2808_, lean_object* v_args_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_2806_, v_k_2807_, v_name_2808_, v_args_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec(v_a_2810_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object* v_k_2817_, lean_object* v_fvarId_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_2817_, v_fvarId_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object* v_decl_2826_, lean_object* v_k_2827_, lean_object* v_name_2828_, lean_object* v_numParams_2829_, lean_object* v_args_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_2826_, v_k_2827_, v_name_2828_, v_numParams_2829_, v_args_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object* v_fvarId_2838_, lean_object* v_sz_2839_, lean_object* v_i_2840_, lean_object* v_bs_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
size_t v_sz_boxed_2848_; size_t v_i_boxed_2849_; lean_object* v_res_2850_; 
v_sz_boxed_2848_ = lean_unbox_usize(v_sz_2839_);
lean_dec(v_sz_2839_);
v_i_boxed_2849_ = lean_unbox_usize(v_i_2840_);
lean_dec(v_i_2840_);
v_res_2850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2838_, v_sz_boxed_2848_, v_i_boxed_2849_, v_bs_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object* v_k_2851_, lean_object* v_decl_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_2851_, v_decl_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* v_decl_2860_, lean_object* v_k_2861_, lean_object* v_ctorInfo_2862_, lean_object* v_fields_2863_, lean_object* v_irArgs_2864_, lean_object* v_i_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2860_, v_k_2861_, v_ctorInfo_2862_, v_fields_2863_, v_irArgs_2864_, v_i_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
lean_dec(v_a_2866_);
lean_dec_ref(v_irArgs_2864_);
lean_dec_ref(v_fields_2863_);
lean_dec_ref(v_ctorInfo_2862_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object* v_decl_2873_, lean_object* v_k_2874_, lean_object* v_name_2875_, lean_object* v_numParams_2876_, lean_object* v_args_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_2873_, v_k_2874_, v_name_2875_, v_numParams_2876_, v_args_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
lean_dec(v_a_2878_);
lean_dec_ref(v_args_2877_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object* v_discr_2885_, lean_object* v_alt_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_discr_2885_, v_alt_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(lean_object* v_discr_2894_, lean_object* v_k_2895_, lean_object* v_ctorInfo_2896_, lean_object* v_spills_2897_, lean_object* v_params_2898_, lean_object* v_fields_2899_, lean_object* v_i_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2894_, v_k_2895_, v_ctorInfo_2896_, v_spills_2897_, v_params_2898_, v_fields_2899_, v_i_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
lean_dec(v_a_2901_);
lean_dec_ref(v_fields_2899_);
lean_dec_ref(v_params_2898_);
lean_dec_ref(v_spills_2897_);
lean_dec_ref(v_ctorInfo_2896_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(lean_object* v_c_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_c_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(lean_object* v_decl_2916_, lean_object* v_k_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2916_, v_k_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
lean_dec(v_a_2920_);
lean_dec_ref(v_a_2919_);
lean_dec(v_a_2918_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(lean_object* v_00_u03b1_2925_, lean_object* v_msg_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_msg_2926_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(lean_object* v_00_u03b1_2934_, lean_object* v_msg_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(v_00_u03b1_2934_, v_msg_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(size_t v_sz_2943_, size_t v_i_2944_, lean_object* v_bs_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2943_, v_i_2944_, v_bs_2945_, v___y_2946_, v___y_2948_, v___y_2949_, v___y_2950_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(lean_object* v_sz_2953_, lean_object* v_i_2954_, lean_object* v_bs_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
size_t v_sz_boxed_2962_; size_t v_i_boxed_2963_; lean_object* v_res_2964_; 
v_sz_boxed_2962_ = lean_unbox_usize(v_sz_2953_);
lean_dec(v_sz_2953_);
v_i_boxed_2963_ = lean_unbox_usize(v_i_2954_);
lean_dec(v_i_2954_);
v_res_2964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(v_sz_boxed_2962_, v_i_boxed_2963_, v_bs_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(lean_object* v_as_2965_, size_t v_i_2966_, size_t v_stop_2967_, lean_object* v_b_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_2965_, v_i_2966_, v_stop_2967_, v_b_2968_, v___y_2969_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(lean_object* v_as_2976_, lean_object* v_i_2977_, lean_object* v_stop_2978_, lean_object* v_b_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
size_t v_i_boxed_2986_; size_t v_stop_boxed_2987_; lean_object* v_res_2988_; 
v_i_boxed_2986_ = lean_unbox_usize(v_i_2977_);
lean_dec(v_i_2977_);
v_stop_boxed_2987_ = lean_unbox_usize(v_stop_2978_);
lean_dec(v_stop_2978_);
v_res_2988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(v_as_2976_, v_i_boxed_2986_, v_stop_boxed_2987_, v_b_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v_as_2976_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(lean_object* v_upperBound_2989_, lean_object* v_params_2990_, lean_object* v___x_2991_, lean_object* v_discr_2992_, lean_object* v_inst_2993_, lean_object* v_R_2994_, lean_object* v_a_2995_, lean_object* v_b_2996_, lean_object* v_c_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_2989_, v_params_2990_, v___x_2991_, v_discr_2992_, v_a_2995_, v_b_2996_, v___y_2998_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(lean_object* v_upperBound_3005_, lean_object* v_params_3006_, lean_object* v___x_3007_, lean_object* v_discr_3008_, lean_object* v_inst_3009_, lean_object* v_R_3010_, lean_object* v_a_3011_, lean_object* v_b_3012_, lean_object* v_c_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(v_upperBound_3005_, v_params_3006_, v___x_3007_, v_discr_3008_, v_inst_3009_, v_R_3010_, v_a_3011_, v_b_3012_, v_c_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec(v___x_3007_);
lean_dec_ref(v_params_3006_);
lean_dec(v_upperBound_3005_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(size_t v_sz_3021_, size_t v_i_3022_, lean_object* v_bs_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_sz_3021_, v_i_3022_, v_bs_3023_, v___y_3024_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(lean_object* v_sz_3031_, lean_object* v_i_3032_, lean_object* v_bs_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
size_t v_sz_boxed_3040_; size_t v_i_boxed_3041_; lean_object* v_res_3042_; 
v_sz_boxed_3040_ = lean_unbox_usize(v_sz_3031_);
lean_dec(v_sz_3031_);
v_i_boxed_3041_ = lean_unbox_usize(v_i_3032_);
lean_dec(v_i_3032_);
v_res_3042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(v_sz_boxed_3040_, v_i_boxed_3041_, v_bs_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14(lean_object* v_upperBound_3043_, lean_object* v_fieldInfo_3044_, lean_object* v___x_3045_, lean_object* v_inst_3046_, lean_object* v_R_3047_, lean_object* v_a_3048_, lean_object* v_b_3049_, lean_object* v_c_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___redArg(v_upperBound_3043_, v_fieldInfo_3044_, v___x_3045_, v_a_3048_, v_b_3049_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14___boxed(lean_object* v_upperBound_3058_, lean_object* v_fieldInfo_3059_, lean_object* v___x_3060_, lean_object* v_inst_3061_, lean_object* v_R_3062_, lean_object* v_a_3063_, lean_object* v_b_3064_, lean_object* v_c_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__14(v_upperBound_3058_, v_fieldInfo_3059_, v___x_3060_, v_inst_3061_, v_R_3062_, v_a_3063_, v_b_3064_, v_c_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___x_3060_);
lean_dec_ref(v_fieldInfo_3059_);
lean_dec(v_upperBound_3058_);
return v_res_3072_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0));
v___x_3075_ = l_Lean_stringToMessageData(v___x_3074_);
return v___x_3075_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2));
v___x_3078_ = l_Lean_stringToMessageData(v___x_3077_);
return v___x_3078_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4));
v___x_3081_ = l_Lean_stringToMessageData(v___x_3080_);
return v___x_3081_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6));
v___x_3084_ = l_Lean_stringToMessageData(v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(lean_object* v_decl_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_toSignature_3092_; lean_object* v_value_3093_; uint8_t v_recursive_3094_; lean_object* v_inlineAttr_x3f_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3227_; 
v_toSignature_3092_ = lean_ctor_get(v_decl_3085_, 0);
v_value_3093_ = lean_ctor_get(v_decl_3085_, 1);
v_recursive_3094_ = lean_ctor_get_uint8(v_decl_3085_, sizeof(void*)*3);
v_inlineAttr_x3f_3095_ = lean_ctor_get(v_decl_3085_, 2);
v_isSharedCheck_3227_ = !lean_is_exclusive(v_decl_3085_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3097_ = v_decl_3085_;
v_isShared_3098_ = v_isSharedCheck_3227_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_inlineAttr_x3f_3095_);
lean_inc(v_value_3093_);
lean_inc(v_toSignature_3092_);
lean_dec(v_decl_3085_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3227_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v_name_3099_; lean_object* v_levelParams_3100_; lean_object* v_type_3101_; lean_object* v_params_3102_; uint8_t v_safe_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3226_; 
v_name_3099_ = lean_ctor_get(v_toSignature_3092_, 0);
v_levelParams_3100_ = lean_ctor_get(v_toSignature_3092_, 1);
v_type_3101_ = lean_ctor_get(v_toSignature_3092_, 2);
v_params_3102_ = lean_ctor_get(v_toSignature_3092_, 3);
v_safe_3103_ = lean_ctor_get_uint8(v_toSignature_3092_, sizeof(void*)*4);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_toSignature_3092_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3105_ = v_toSignature_3092_;
v_isShared_3106_ = v_isSharedCheck_3226_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_params_3102_);
lean_inc(v_type_3101_);
lean_inc(v_levelParams_3100_);
lean_inc(v_name_3099_);
lean_dec(v_toSignature_3092_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3226_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
size_t v_sz_3107_; size_t v___x_3108_; lean_object* v___x_3109_; 
v_sz_3107_ = lean_array_size(v_params_3102_);
v___x_3108_ = ((size_t)0ULL);
lean_inc_ref(v_params_3102_);
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_3107_, v___x_3108_, v_params_3102_, v_a_3086_, v_a_3088_, v_a_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref_known(v___x_3109_, 1);
v___x_3111_ = lean_array_get_size(v_params_3102_);
lean_dec_ref(v_params_3102_);
v___x_3112_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_3101_, v___x_3111_, v_a_3089_, v_a_3090_);
lean_dec_ref(v_type_3101_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3209_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3115_ = v___x_3112_;
v_isShared_3116_ = v_isSharedCheck_3209_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3209_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; lean_object* v_env_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3117_ = lean_st_ref_get(v_a_3090_);
v_env_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc_ref(v_env_3118_);
lean_dec(v___x_3117_);
v___x_3119_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
lean_inc(v_name_3099_);
v___x_3120_ = l_Lean_TagAttribute_hasTag(v___x_3119_, v_env_3118_, v_name_3099_);
if (lean_obj_tag(v_value_3093_) == 0)
{
lean_object* v_code_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3171_; 
lean_del_object(v___x_3115_);
v_code_3121_ = lean_ctor_get(v_value_3093_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_value_3093_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3123_ = v_value_3093_;
v_isShared_3124_ = v_isSharedCheck_3171_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_code_3121_);
lean_dec(v_value_3093_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3171_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; 
if (v___x_3120_ == 0)
{
v___y_3126_ = v_a_3086_;
v___y_3127_ = v_a_3087_;
v___y_3128_ = v_a_3088_;
v___y_3129_ = v_a_3089_;
v___y_3130_ = v_a_3090_;
goto v___jp_3125_;
}
else
{
lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_del_object(v___x_3123_);
lean_dec_ref(v_code_3121_);
lean_dec(v_a_3113_);
lean_dec(v_a_3110_);
lean_del_object(v___x_3105_);
lean_dec(v_levelParams_3100_);
lean_del_object(v___x_3097_);
lean_dec(v_inlineAttr_x3f_3095_);
v___x_3157_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1);
v___x_3158_ = l_Lean_MessageData_ofName(v_name_3099_);
v___x_3159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3157_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3);
v___x_3161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3159_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_3161_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3162_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3162_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
v___jp_3125_:
{
lean_object* v___x_3131_; 
v___x_3131_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_3121_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3148_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3134_ = v___x_3131_;
v_isShared_3135_ = v_isSharedCheck_3148_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3131_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3148_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 3, v_a_3110_);
lean_ctor_set(v___x_3105_, 2, v_a_3113_);
v___x_3137_ = v___x_3105_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_name_3099_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_levelParams_3100_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_a_3113_);
lean_ctor_set(v_reuseFailAlloc_3147_, 3, v_a_3110_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, sizeof(void*)*4, v_safe_3103_);
v___x_3137_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3139_; 
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v_a_3132_);
v___x_3139_ = v___x_3123_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3132_);
v___x_3139_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3141_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_3139_);
lean_ctor_set(v___x_3097_, 0, v___x_3137_);
v___x_3141_ = v___x_3097_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v_inlineAttr_x3f_3095_);
lean_ctor_set_uint8(v_reuseFailAlloc_3145_, sizeof(void*)*3, v_recursive_3094_);
v___x_3141_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3143_; 
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v___x_3141_);
v___x_3143_ = v___x_3134_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_del_object(v___x_3123_);
lean_dec(v_a_3113_);
lean_dec(v_a_3110_);
lean_del_object(v___x_3105_);
lean_dec(v_levelParams_3100_);
lean_dec(v_name_3099_);
lean_del_object(v___x_3097_);
lean_dec(v_inlineAttr_x3f_3095_);
v_a_3149_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3131_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3131_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
}
else
{
lean_object* v_externAttrData_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3208_; 
v_externAttrData_3172_ = lean_ctor_get(v_value_3093_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_value_3093_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3174_ = v_value_3093_;
v_isShared_3175_ = v_isSharedCheck_3208_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_externAttrData_3172_);
lean_dec(v_value_3093_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3208_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v_resultType_3177_; 
if (v___x_3120_ == 0)
{
v_resultType_3177_ = v_a_3113_;
goto v___jp_3176_;
}
else
{
uint8_t v___x_3190_; 
v___x_3190_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_3113_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; 
lean_dec(v_a_3113_);
v___x_3191_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
v_resultType_3177_ = v___x_3191_;
goto v___jp_3176_;
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_del_object(v___x_3174_);
lean_dec(v_externAttrData_3172_);
lean_del_object(v___x_3115_);
lean_dec(v_a_3110_);
lean_del_object(v___x_3105_);
lean_dec(v_levelParams_3100_);
lean_del_object(v___x_3097_);
lean_dec(v_inlineAttr_x3f_3095_);
v___x_3192_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5);
v___x_3193_ = l_Lean_MessageData_ofName(v_name_3099_);
v___x_3194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3192_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7);
v___x_3196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3194_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = l_Lean_MessageData_ofExpr(v_a_3113_);
v___x_3198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3196_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_3198_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
v___jp_3176_:
{
lean_object* v___x_3179_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 3, v_a_3110_);
lean_ctor_set(v___x_3105_, 2, v_resultType_3177_);
v___x_3179_ = v___x_3105_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_name_3099_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_levelParams_3100_);
lean_ctor_set(v_reuseFailAlloc_3189_, 2, v_resultType_3177_);
lean_ctor_set(v_reuseFailAlloc_3189_, 3, v_a_3110_);
lean_ctor_set_uint8(v_reuseFailAlloc_3189_, sizeof(void*)*4, v_safe_3103_);
v___x_3179_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3181_; 
if (v_isShared_3175_ == 0)
{
v___x_3181_ = v___x_3174_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_externAttrData_3172_);
v___x_3181_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3183_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_3181_);
lean_ctor_set(v___x_3097_, 0, v___x_3179_);
v___x_3183_ = v___x_3097_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v___x_3181_);
lean_ctor_set(v_reuseFailAlloc_3187_, 2, v_inlineAttr_x3f_3095_);
lean_ctor_set_uint8(v_reuseFailAlloc_3187_, sizeof(void*)*3, v_recursive_3094_);
v___x_3183_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3185_; 
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v___x_3183_);
v___x_3185_ = v___x_3115_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
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
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v_a_3110_);
lean_del_object(v___x_3105_);
lean_dec(v_levelParams_3100_);
lean_dec(v_name_3099_);
lean_del_object(v___x_3097_);
lean_dec(v_inlineAttr_x3f_3095_);
lean_dec_ref(v_value_3093_);
v_a_3210_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3112_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3112_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_del_object(v___x_3105_);
lean_dec_ref(v_params_3102_);
lean_dec_ref(v_type_3101_);
lean_dec(v_levelParams_3100_);
lean_dec(v_name_3099_);
lean_del_object(v___x_3097_);
lean_dec(v_inlineAttr_x3f_3095_);
lean_dec_ref(v_value_3093_);
v_a_3218_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3109_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3109_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___boxed(lean_object* v_decl_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(lean_object* v_decl_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; lean_object* v___x_3245_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc_n(v_a_3244_, 2);
lean_dec_ref_known(v___x_3243_, 1);
v___x_3245_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_3244_, v_a_3241_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; 
v_unused_3253_ = lean_ctor_get(v___x_3245_, 0);
lean_dec(v_unused_3253_);
v___x_3247_ = v___x_3245_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_dec(v___x_3245_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 0, v_a_3244_);
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3244_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec(v_a_3244_);
v_a_3254_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3245_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3245_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
else
{
return v___x_3243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go___boxed(lean_object* v_decl_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_);
lean_dec(v_a_3267_);
lean_dec_ref(v_a_3266_);
lean_dec(v_a_3265_);
lean_dec_ref(v_a_3264_);
lean_dec(v_a_3263_);
return v_res_3269_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3270_ = lean_box(0);
v___x_3271_ = lean_unsigned_to_nat(16u);
v___x_3272_ = lean_mk_array(v___x_3271_, v___x_3270_);
return v___x_3272_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0);
v___x_3274_ = lean_unsigned_to_nat(0u);
v___x_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
lean_ctor_set(v___x_3275_, 1, v___x_3273_);
return v___x_3275_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1);
v___x_3277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(lean_object* v_decl_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3284_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2);
v___x_3285_ = lean_st_mk_ref(v___x_3284_);
v___x_3286_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_3278_, v___x_3285_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3295_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3295_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3295_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3291_ = lean_st_ref_get(v___x_3285_);
lean_dec(v___x_3285_);
lean_dec(v___x_3291_);
if (v_isShared_3290_ == 0)
{
v___x_3293_ = v___x_3289_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3287_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
else
{
lean_dec(v___x_3285_);
return v___x_3286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___boxed(lean_object* v_decl_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_decl_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(size_t v_sz_3303_, size_t v_i_3304_, lean_object* v_bs_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
uint8_t v___x_3311_; 
v___x_3311_ = lean_usize_dec_lt(v_i_3304_, v_sz_3303_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3312_; 
v___x_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3312_, 0, v_bs_3305_);
return v___x_3312_;
}
else
{
lean_object* v_v_3313_; lean_object* v___x_3314_; lean_object* v_bs_x27_3315_; lean_object* v___x_3316_; 
v_v_3313_ = lean_array_uget(v_bs_3305_, v_i_3304_);
v___x_3314_ = lean_unsigned_to_nat(0u);
v_bs_x27_3315_ = lean_array_uset(v_bs_3305_, v_i_3304_, v___x_3314_);
v___x_3316_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_v_3313_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; size_t v___x_3318_; size_t v___x_3319_; lean_object* v___x_3320_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v___x_3316_, 1);
v___x_3318_ = ((size_t)1ULL);
v___x_3319_ = lean_usize_add(v_i_3304_, v___x_3318_);
v___x_3320_ = lean_array_uset(v_bs_x27_3315_, v_i_3304_, v_a_3317_);
v_i_3304_ = v___x_3319_;
v_bs_3305_ = v___x_3320_;
goto _start;
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec_ref(v_bs_x27_3315_);
v_a_3322_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3316_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3316_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0___boxed(lean_object* v_sz_3330_, lean_object* v_i_3331_, lean_object* v_bs_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
size_t v_sz_boxed_3338_; size_t v_i_boxed_3339_; lean_object* v_res_3340_; 
v_sz_boxed_3338_ = lean_unbox_usize(v_sz_3330_);
lean_dec(v_sz_3330_);
v_i_boxed_3339_ = lean_unbox_usize(v_i_3331_);
lean_dec(v_i_3331_);
v_res_3340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_boxed_3338_, v_i_boxed_3339_, v_bs_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0(lean_object* v_x_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
size_t v_sz_3347_; size_t v___x_3348_; lean_object* v___x_3349_; 
v_sz_3347_ = lean_array_size(v_x_3341_);
v___x_3348_ = ((size_t)0ULL);
v___x_3349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_3347_, v___x_3348_, v_x_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0___boxed(lean_object* v_x_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_Compiler_LCNF_toImpure___lam__0(v_x_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3407_; uint8_t v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3407_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3408_ = 1;
v___x_3409_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3410_ = l_Lean_registerTraceClass(v___x_3407_, v___x_3408_, v___x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2____boxed(lean_object* v_a_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
return v_res_3412_;
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
