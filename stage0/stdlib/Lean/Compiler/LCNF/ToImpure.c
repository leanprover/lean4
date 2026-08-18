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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_toImpureType(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isVoid(lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_getCtorLayout(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_nameToImpureType(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CtorInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
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
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 150, .m_capacity = 150, .m_length = 149, .m_data = "Marks an extern definition to be guaranteed to always return tagged values.\nThis information is used to optimize reference counting in the compiler.\n"};
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
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_liftIOCore___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "obj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value),LEAN_SCALAR_PTR_LITERAL(240, 235, 44, 74, 242, 121, 239, 90)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__14___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__14___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__14(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Data.DHashMap.Internal.Defs"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 37, .m_data = "Std.DHashMap.Internal.Raw₀.Const.get!"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "assertion violation: c.alts.size == 1\n      "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__3;
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
lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___f_54_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_55_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_56_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_57_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_58_ = 0;
v___x_59_ = lean_box(2);
v___x_60_ = l_Lean_registerTagAttribute(v___x_55_, v___x_56_, v___f_54_, v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_66_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0));
v___x_67_ = l_Lean_addBuiltinDocString(v___x_65_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3(){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_97_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6));
v___x_98_ = l_Lean_addBuiltinDeclarationRanges(v___x_96_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___boxed(lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3();
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(lean_object* v_____do__lift_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_subst_108_; lean_object* v___x_109_; 
v_subst_108_ = lean_ctor_get(v_____do__lift_101_, 0);
lean_inc_ref(v_subst_108_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v_subst_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed(lean_object* v_____do__lift_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(v_____do__lift_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v_____do__lift_110_);
return v_res_117_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_instMonadEIO(lean_box(0));
return v___x_118_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0);
v___x_120_ = l_StateRefT_x27_instMonad___redArg(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue(void){
_start:
{
lean_object* v___x_149_; lean_object* v_toApplicative_150_; lean_object* v_toFunctor_151_; lean_object* v_toSeq_152_; lean_object* v_toSeqLeft_153_; lean_object* v_toSeqRight_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___x_159_; lean_object* v___f_160_; lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_toApplicative_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_196_; 
v___x_149_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_150_ = lean_ctor_get(v___x_149_, 0);
v_toFunctor_151_ = lean_ctor_get(v_toApplicative_150_, 0);
v_toSeq_152_ = lean_ctor_get(v_toApplicative_150_, 2);
v_toSeqLeft_153_ = lean_ctor_get(v_toApplicative_150_, 3);
v_toSeqRight_154_ = lean_ctor_get(v_toApplicative_150_, 4);
v___f_155_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_156_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref_n(v_toFunctor_151_, 2);
v___f_157_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_157_, 0, v_toFunctor_151_);
v___f_158_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_158_, 0, v_toFunctor_151_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___f_157_);
lean_ctor_set(v___x_159_, 1, v___f_158_);
lean_inc(v_toSeqRight_154_);
v___f_160_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_160_, 0, v_toSeqRight_154_);
lean_inc(v_toSeqLeft_153_);
v___f_161_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_161_, 0, v_toSeqLeft_153_);
lean_inc(v_toSeq_152_);
v___f_162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_162_, 0, v_toSeq_152_);
v___x_163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_163_, 0, v___x_159_);
lean_ctor_set(v___x_163_, 1, v___f_155_);
lean_ctor_set(v___x_163_, 2, v___f_162_);
lean_ctor_set(v___x_163_, 3, v___f_161_);
lean_ctor_set(v___x_163_, 4, v___f_160_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___f_156_);
v___x_165_ = l_StateRefT_x27_instMonad___redArg(v___x_164_);
v_toApplicative_166_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; 
v_unused_197_ = lean_ctor_get(v___x_165_, 1);
lean_dec(v_unused_197_);
v___x_168_ = v___x_165_;
v_isShared_169_ = v_isSharedCheck_196_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_toApplicative_166_);
lean_dec(v___x_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_196_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_toFunctor_170_; lean_object* v_toSeq_171_; lean_object* v_toSeqLeft_172_; lean_object* v_toSeqRight_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_194_; 
v_toFunctor_170_ = lean_ctor_get(v_toApplicative_166_, 0);
v_toSeq_171_ = lean_ctor_get(v_toApplicative_166_, 2);
v_toSeqLeft_172_ = lean_ctor_get(v_toApplicative_166_, 3);
v_toSeqRight_173_ = lean_ctor_get(v_toApplicative_166_, 4);
v_isSharedCheck_194_ = !lean_is_exclusive(v_toApplicative_166_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v_toApplicative_166_, 1);
lean_dec(v_unused_195_);
v___x_175_ = v_toApplicative_166_;
v_isShared_176_ = v_isSharedCheck_194_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_toSeqRight_173_);
lean_inc(v_toSeqLeft_172_);
lean_inc(v_toSeq_171_);
lean_inc(v_toFunctor_170_);
lean_dec(v_toApplicative_166_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_194_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___f_180_; lean_object* v___f_181_; lean_object* v___x_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___x_187_; 
v___f_177_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4));
v___f_178_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_179_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_170_);
v___f_180_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_180_, 0, v_toFunctor_170_);
v___f_181_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_181_, 0, v_toFunctor_170_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___f_180_);
lean_ctor_set(v___x_182_, 1, v___f_181_);
v___f_183_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_183_, 0, v_toSeqRight_173_);
v___f_184_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_184_, 0, v_toSeqLeft_172_);
v___f_185_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_185_, 0, v_toSeq_171_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 4, v___f_183_);
lean_ctor_set(v___x_175_, 3, v___f_184_);
lean_ctor_set(v___x_175_, 2, v___f_185_);
lean_ctor_set(v___x_175_, 1, v___f_178_);
lean_ctor_set(v___x_175_, 0, v___x_182_);
v___x_187_ = v___x_175_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___f_178_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v___f_185_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v___f_184_);
lean_ctor_set(v_reuseFailAlloc_193_, 4, v___f_183_);
v___x_187_ = v_reuseFailAlloc_193_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_189_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___f_179_);
lean_ctor_set(v___x_168_, 0, v___x_187_);
v___x_189_ = v___x_168_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___f_179_);
v___x_189_ = v_reuseFailAlloc_192_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18));
v___x_191_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_191_, 0, lean_box(0));
lean_closure_set(v___x_191_, 1, lean_box(0));
lean_closure_set(v___x_191_, 2, v___x_189_);
lean_closure_set(v___x_191_, 3, lean_box(0));
lean_closure_set(v___x_191_, 4, lean_box(0));
lean_closure_set(v___x_191_, 5, v___x_190_);
lean_closure_set(v___x_191_, 6, v___f_177_);
return v___x_191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(lean_object* v_f_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; lean_object* v_subst_206_; lean_object* v_jpParamMask_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_218_; 
v___x_205_ = lean_st_ref_take(v___y_199_);
v_subst_206_ = lean_ctor_get(v___x_205_, 0);
v_jpParamMask_207_ = lean_ctor_get(v___x_205_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_218_ == 0)
{
v___x_209_ = v___x_205_;
v_isShared_210_ = v_isSharedCheck_218_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_jpParamMask_207_);
lean_inc(v_subst_206_);
lean_dec(v___x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_218_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_apply_1(v_f_198_, v_subst_206_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_211_);
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_jpParamMask_207_);
v___x_213_ = v_reuseFailAlloc_217_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_st_ref_put(v___y_199_, v___x_213_);
v___x_215_ = lean_box(0);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed(lean_object* v_f_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(v_f_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(lean_object* v_m_229_, lean_object* v_query_230_, lean_object* v_x_231_, lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
lean_object* v_zero_234_; uint8_t v_isZero_235_; 
v_zero_234_ = lean_unsigned_to_nat(0u);
v_isZero_235_ = lean_nat_dec_eq(v_x_232_, v_zero_234_);
if (v_isZero_235_ == 1)
{
lean_dec(v_x_233_);
lean_dec(v_x_232_);
if (lean_obj_tag(v_x_231_) == 0)
{
lean_object* v___x_236_; 
v___x_236_ = lean_box(2);
return v___x_236_;
}
else
{
lean_object* v_val_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v_val_237_ = lean_ctor_get(v_x_231_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v_x_231_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_val_237_);
lean_dec(v_x_231_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_val_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v_keyArray_245_; lean_object* v_valueArray_246_; lean_object* v___x_247_; uint8_t v_isSome_248_; 
v_keyArray_245_ = lean_ctor_get(v_m_229_, 1);
v_valueArray_246_ = lean_ctor_get(v_m_229_, 2);
v___x_247_ = lean_array_fget_borrowed(v_keyArray_245_, v_x_233_);
v_isSome_248_ = lean_noption_is_some(v___x_247_);
if (v_isSome_248_ == 0)
{
lean_dec(v_x_232_);
if (lean_obj_tag(v_x_231_) == 0)
{
lean_object* v___x_249_; 
v___x_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_249_, 0, v_x_233_);
return v___x_249_;
}
else
{
lean_object* v_val_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_dec(v_x_233_);
v_val_250_ = lean_ctor_get(v_x_231_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v_x_231_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_val_250_);
lean_dec(v_x_231_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_val_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
else
{
lean_object* v_one_258_; lean_object* v_n_259_; lean_object* v___y_261_; 
v_one_258_ = lean_unsigned_to_nat(1u);
v_n_259_ = lean_nat_sub(v_x_232_, v_one_258_);
lean_dec(v_x_232_);
if (v_isSome_248_ == 0)
{
goto v___jp_267_;
}
else
{
lean_object* v___x_269_; uint8_t v_isSome_270_; 
v___x_269_ = lean_array_fget_borrowed(v_valueArray_246_, v_x_233_);
v_isSome_270_ = lean_noption_is_some(v___x_269_);
if (v_isSome_270_ == 0)
{
goto v___jp_267_;
}
else
{
lean_object* v_val_271_; uint8_t v___x_272_; 
lean_inc(v___x_247_);
v_val_271_ = lean_noption_get(v___x_247_);
v___x_272_ = l_Lean_instBEqFVarId_beq(v_val_271_, v_query_230_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
lean_dec(v_val_271_);
v___x_273_ = lean_array_get_size(v_keyArray_245_);
v___x_274_ = lean_nat_add(v_x_233_, v_one_258_);
lean_dec(v_x_233_);
v___x_275_ = lean_nat_dec_lt(v___x_274_, v___x_273_);
if (v___x_275_ == 0)
{
lean_dec(v___x_274_);
v_x_232_ = v_n_259_;
v_x_233_ = v_zero_234_;
goto _start;
}
else
{
v_x_232_ = v_n_259_;
v_x_233_ = v___x_274_;
goto _start;
}
}
else
{
lean_object* v_val_278_; lean_object* v___x_279_; 
lean_dec(v_n_259_);
lean_dec(v_x_231_);
lean_inc(v___x_269_);
v_val_278_ = lean_noption_get(v___x_269_);
v___x_279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_279_, 0, v_x_233_);
lean_ctor_set(v___x_279_, 1, v_val_271_);
lean_ctor_set(v___x_279_, 2, v_val_278_);
return v___x_279_;
}
}
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_262_ = lean_array_get_size(v_keyArray_245_);
v___x_263_ = lean_nat_add(v_x_233_, v_one_258_);
lean_dec(v_x_233_);
v___x_264_ = lean_nat_dec_lt(v___x_263_, v___x_262_);
if (v___x_264_ == 0)
{
lean_dec(v___x_263_);
v_x_231_ = v___y_261_;
v_x_232_ = v_n_259_;
v_x_233_ = v_zero_234_;
goto _start;
}
else
{
v_x_231_ = v___y_261_;
v_x_232_ = v_n_259_;
v_x_233_ = v___x_263_;
goto _start;
}
}
v___jp_267_:
{
if (lean_obj_tag(v_x_231_) == 0)
{
lean_object* v___x_268_; 
lean_inc(v_x_233_);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v_x_233_);
v___y_261_ = v___x_268_;
goto v___jp_260_;
}
else
{
v___y_261_ = v_x_231_;
goto v___jp_260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg___boxed(lean_object* v_m_280_, lean_object* v_query_281_, lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_m_280_, v_query_281_, v_x_282_, v_x_283_, v_x_284_);
lean_dec(v_query_281_);
lean_dec_ref(v_m_280_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(lean_object* v_m_286_, lean_object* v_query_287_){
_start:
{
lean_object* v_keyArray_288_; lean_object* v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v_fold_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_keyArray_288_ = lean_ctor_get(v_m_286_, 1);
v___x_289_ = lean_array_get_size(v_keyArray_288_);
v___x_290_ = l_Lean_instHashableFVarId_hash(v_query_287_);
v___x_291_ = 32ULL;
v___x_292_ = lean_uint64_shift_right(v___x_290_, v___x_291_);
v_fold_293_ = lean_uint64_xor(v___x_290_, v___x_292_);
v___x_294_ = 16ULL;
v___x_295_ = lean_uint64_shift_right(v_fold_293_, v___x_294_);
v___x_296_ = lean_uint64_xor(v_fold_293_, v___x_295_);
v___x_297_ = lean_uint64_to_usize(v___x_296_);
v___x_298_ = lean_usize_of_nat(v___x_289_);
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_sub(v___x_298_, v___x_299_);
v___x_301_ = lean_usize_land(v___x_297_, v___x_300_);
v___x_302_ = lean_usize_to_nat(v___x_301_);
v___x_303_ = lean_box(0);
v___x_304_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_m_286_, v_query_287_, v___x_303_, v___x_289_, v___x_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg___boxed(lean_object* v_m_305_, lean_object* v_query_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_m_305_, v_query_306_);
lean_dec(v_query_306_);
lean_dec_ref(v_m_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2_spec__3___redArg(lean_object* v_b_308_, lean_object* v_acc_309_, lean_object* v_i_310_){
_start:
{
lean_object* v___y_312_; lean_object* v_keyArray_320_; lean_object* v_valueArray_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v_keyArray_320_ = lean_ctor_get(v_b_308_, 1);
v_valueArray_321_ = lean_ctor_get(v_b_308_, 2);
v___x_322_ = lean_array_get_size(v_keyArray_320_);
v___x_323_ = lean_nat_dec_lt(v_i_310_, v___x_322_);
if (v___x_323_ == 0)
{
lean_dec(v_i_310_);
return v_acc_309_;
}
else
{
lean_object* v___x_324_; uint8_t v_isSome_325_; 
v___x_324_ = lean_array_fget_borrowed(v_keyArray_320_, v_i_310_);
v_isSome_325_ = lean_noption_is_some(v___x_324_);
if (v_isSome_325_ == 0)
{
goto v___jp_316_;
}
else
{
lean_object* v___x_326_; uint8_t v_isSome_327_; 
v___x_326_ = lean_array_fget_borrowed(v_valueArray_321_, v_i_310_);
v_isSome_327_ = lean_noption_is_some(v___x_326_);
if (v_isSome_327_ == 0)
{
goto v___jp_316_;
}
else
{
lean_object* v_val_328_; lean_object* v_val_329_; lean_object* v_i_331_; lean_object* v___x_336_; 
lean_inc(v___x_324_);
v_val_328_ = lean_noption_get(v___x_324_);
lean_inc(v___x_326_);
v_val_329_ = lean_noption_get(v___x_326_);
v___x_336_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_acc_309_, v_val_328_);
switch(lean_obj_tag(v___x_336_))
{
case 0:
{
lean_object* v_index_337_; lean_object* v_size_338_; lean_object* v___x_339_; 
v_index_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_index_337_);
lean_dec_ref_known(v___x_336_, 3);
v_size_338_ = lean_ctor_get(v_acc_309_, 0);
lean_inc(v_size_338_);
v___x_339_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_309_, v_size_338_, v_index_337_, v_val_328_, v_val_329_);
lean_dec(v_index_337_);
v___y_312_ = v___x_339_;
goto v___jp_311_;
}
case 1:
{
lean_object* v_index_340_; 
v_index_340_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_index_340_);
lean_dec_ref_known(v___x_336_, 1);
v_i_331_ = v_index_340_;
goto v___jp_330_;
}
default: 
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_309_, v___x_341_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_index_343_; 
v_index_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_index_343_);
lean_dec_ref_known(v___x_342_, 1);
v_i_331_ = v_index_343_;
goto v___jp_330_;
}
else
{
lean_dec(v_val_329_);
lean_dec(v_val_328_);
v___y_312_ = v_acc_309_;
goto v___jp_311_;
}
}
}
v___jp_330_:
{
lean_object* v_size_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_size_332_ = lean_ctor_get(v_acc_309_, 0);
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_add(v_size_332_, v___x_333_);
v___x_335_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_309_, v___x_334_, v_i_331_, v_val_328_, v_val_329_);
lean_dec(v_i_331_);
v___y_312_ = v___x_335_;
goto v___jp_311_;
}
}
}
}
v___jp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = lean_nat_add(v_i_310_, v___x_313_);
lean_dec(v_i_310_);
v_acc_309_ = v___y_312_;
v_i_310_ = v___x_314_;
goto _start;
}
v___jp_316_:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_add(v_i_310_, v___x_317_);
lean_dec(v_i_310_);
v_i_310_ = v___x_318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_344_, lean_object* v_acc_345_, lean_object* v_i_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2_spec__3___redArg(v_b_344_, v_acc_345_, v_i_346_);
lean_dec_ref(v_b_344_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2___redArg(lean_object* v_init_348_, lean_object* v_b_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2_spec__3___redArg(v_b_349_, v_init_348_, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2___redArg___boxed(lean_object* v_init_352_, lean_object* v_b_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2___redArg(v_init_352_, v_b_353_);
lean_dec_ref(v_b_353_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(lean_object* v_m_355_){
_start:
{
lean_object* v_keyArray_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_cellCount_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_target_363_; lean_object* v___x_364_; 
v_keyArray_356_ = lean_ctor_get(v_m_355_, 1);
v___x_357_ = lean_array_get_size(v_keyArray_356_);
v___x_358_ = lean_unsigned_to_nat(2u);
v_cellCount_359_ = lean_nat_mul(v___x_357_, v___x_358_);
v___x_360_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_359_);
v___x_361_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_359_);
v___x_362_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_359_);
v_target_363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_363_, 0, v___x_360_);
lean_ctor_set(v_target_363_, 1, v___x_361_);
lean_ctor_set(v_target_363_, 2, v___x_362_);
v___x_364_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2___redArg(v_target_363_, v_m_355_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg___boxed(lean_object* v_m_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_m_365_);
lean_dec_ref(v_m_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(lean_object* v_p_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_fvarId_373_; lean_object* v_binderName_374_; lean_object* v_type_375_; uint8_t v_borrow_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_505_; 
v_fvarId_373_ = lean_ctor_get(v_p_367_, 0);
v_binderName_374_ = lean_ctor_get(v_p_367_, 1);
v_type_375_ = lean_ctor_get(v_p_367_, 2);
v_borrow_376_ = lean_ctor_get_uint8(v_p_367_, sizeof(void*)*3);
v_isSharedCheck_505_ = !lean_is_exclusive(v_p_367_);
if (v_isSharedCheck_505_ == 0)
{
v___x_378_ = v_p_367_;
v_isShared_379_ = v_isSharedCheck_505_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_type_375_);
lean_inc(v_binderName_374_);
lean_inc(v_fvarId_373_);
lean_dec(v_p_367_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_505_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Compiler_LCNF_toImpureType(v_type_375_, v_a_370_, v_a_371_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_496_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_496_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_496_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_496_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___y_386_; lean_object* v_jpParamMask_407_; lean_object* v___y_408_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v_i_419_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v_i_441_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; uint8_t v___y_459_; uint8_t v___x_494_; 
v___x_494_ = l_Lean_Expr_isVoid(v_a_381_);
if (v___x_494_ == 0)
{
uint8_t v___x_495_; 
v___x_495_ = l_Lean_Expr_isErased(v_a_381_);
v___y_459_ = v___x_495_;
goto v___jp_458_;
}
else
{
v___y_459_ = v___x_494_;
goto v___jp_458_;
}
v___jp_385_:
{
lean_object* v___x_387_; lean_object* v_lctx_388_; lean_object* v_nextIdx_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_405_; 
v___x_387_ = lean_st_ref_take(v___y_386_);
v_lctx_388_ = lean_ctor_get(v___x_387_, 0);
v_nextIdx_389_ = lean_ctor_get(v___x_387_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_405_ == 0)
{
v___x_391_ = v___x_387_;
v_isShared_392_ = v_isSharedCheck_405_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_nextIdx_389_);
lean_inc(v_lctx_388_);
lean_dec(v___x_387_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_405_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
uint8_t v___x_393_; lean_object* v___x_395_; 
v___x_393_ = 1;
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 2, v_a_381_);
v___x_395_ = v___x_378_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_fvarId_373_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_binderName_374_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_a_381_);
lean_ctor_set_uint8(v_reuseFailAlloc_404_, sizeof(void*)*3, v_borrow_376_);
v___x_395_ = v_reuseFailAlloc_404_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
lean_inc_ref(v___x_395_);
v___x_396_ = l_Lean_Compiler_LCNF_LCtx_addParam(v___x_393_, v_lctx_388_, v___x_395_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_396_);
v___x_398_ = v___x_391_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_nextIdx_389_);
v___x_398_ = v_reuseFailAlloc_403_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = lean_st_ref_put(v___y_386_, v___x_398_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_395_);
v___x_401_ = v___x_383_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_395_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
v___jp_406_:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___y_408_);
lean_ctor_set(v___x_409_, 1, v_jpParamMask_407_);
v___x_410_ = lean_st_ref_put(v_a_368_, v___x_409_);
v___y_386_ = v_a_369_;
goto v___jp_385_;
}
v___jp_411_:
{
lean_object* v_jpParamMask_414_; 
v_jpParamMask_414_ = lean_ctor_get(v___y_412_, 1);
lean_inc_ref(v_jpParamMask_414_);
lean_dec_ref(v___y_412_);
v_jpParamMask_407_ = v_jpParamMask_414_;
v___y_408_ = v___y_413_;
goto v___jp_406_;
}
v___jp_415_:
{
lean_object* v_size_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_size_420_ = lean_ctor_get(v___y_416_, 0);
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v_size_420_, v___x_421_);
lean_inc(v_fvarId_373_);
v___x_423_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_416_, v___x_422_, v_i_419_, v_fvarId_373_, v___y_418_);
lean_dec(v_i_419_);
v___y_412_ = v___y_417_;
v___y_413_ = v___x_423_;
goto v___jp_411_;
}
v___jp_424_:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v___y_425_);
lean_dec_ref(v___y_425_);
v___x_429_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___x_428_, v_fvarId_373_);
switch(lean_obj_tag(v___x_429_))
{
case 0:
{
lean_object* v_index_430_; lean_object* v_size_431_; lean_object* v___x_432_; 
v_index_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_index_430_);
lean_dec_ref_known(v___x_429_, 3);
v_size_431_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_size_431_);
lean_inc(v_fvarId_373_);
v___x_432_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_428_, v_size_431_, v_index_430_, v_fvarId_373_, v___y_427_);
lean_dec(v_index_430_);
v___y_412_ = v___y_426_;
v___y_413_ = v___x_432_;
goto v___jp_411_;
}
case 1:
{
lean_object* v_index_433_; 
v_index_433_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_index_433_);
lean_dec_ref_known(v___x_429_, 1);
v___y_416_ = v___x_428_;
v___y_417_ = v___y_426_;
v___y_418_ = v___y_427_;
v_i_419_ = v_index_433_;
goto v___jp_415_;
}
default: 
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_428_, v___x_434_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_index_436_; 
v_index_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_index_436_);
lean_dec_ref_known(v___x_435_, 1);
v___y_416_ = v___x_428_;
v___y_417_ = v___y_426_;
v___y_418_ = v___y_427_;
v_i_419_ = v_index_436_;
goto v___jp_415_;
}
else
{
lean_dec(v___y_427_);
v___y_412_ = v___y_426_;
v___y_413_ = v___x_428_;
goto v___jp_411_;
}
}
}
}
v___jp_437_:
{
lean_object* v_size_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_size_442_ = lean_ctor_get(v___y_439_, 0);
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_add(v_size_442_, v___x_443_);
lean_inc(v_fvarId_373_);
v___x_445_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_439_, v___x_444_, v_i_441_, v_fvarId_373_, v___y_440_);
lean_dec(v_i_441_);
v___y_412_ = v___y_438_;
v___y_413_ = v___x_445_;
goto v___jp_411_;
}
v___jp_446_:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___y_449_, v_fvarId_373_);
switch(lean_obj_tag(v___x_450_))
{
case 0:
{
lean_object* v_index_451_; lean_object* v_size_452_; lean_object* v___x_453_; 
v_index_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_index_451_);
lean_dec_ref_known(v___x_450_, 3);
v_size_452_ = lean_ctor_get(v___y_449_, 0);
lean_inc(v_size_452_);
lean_inc(v_fvarId_373_);
v___x_453_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_449_, v_size_452_, v_index_451_, v_fvarId_373_, v___y_448_);
lean_dec(v_index_451_);
v___y_412_ = v___y_447_;
v___y_413_ = v___x_453_;
goto v___jp_411_;
}
case 1:
{
lean_object* v_index_454_; 
v_index_454_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_index_454_);
lean_dec_ref_known(v___x_450_, 1);
v___y_438_ = v___y_447_;
v___y_439_ = v___y_449_;
v___y_440_ = v___y_448_;
v_i_441_ = v_index_454_;
goto v___jp_437_;
}
default: 
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_449_, v___x_455_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_index_457_; 
v_index_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_index_457_);
lean_dec_ref_known(v___x_456_, 1);
v___y_438_ = v___y_447_;
v___y_439_ = v___y_449_;
v___y_440_ = v___y_448_;
v_i_441_ = v_index_457_;
goto v___jp_437_;
}
else
{
lean_dec(v___y_448_);
v___y_412_ = v___y_447_;
v___y_413_ = v___y_449_;
goto v___jp_411_;
}
}
}
}
v___jp_458_:
{
if (v___y_459_ == 0)
{
v___y_386_ = v_a_369_;
goto v___jp_385_;
}
else
{
lean_object* v___x_460_; lean_object* v_subst_461_; lean_object* v_jpParamMask_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_460_ = lean_st_ref_take(v_a_368_);
v_subst_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc_ref(v_subst_461_);
v_jpParamMask_462_ = lean_ctor_get(v___x_460_, 1);
lean_inc_ref(v_jpParamMask_462_);
v___x_463_ = lean_box(0);
v___x_464_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_461_, v_fvarId_373_);
switch(lean_obj_tag(v___x_464_))
{
case 0:
{
lean_object* v_index_465_; lean_object* v_size_466_; lean_object* v___x_467_; 
lean_dec(v___x_460_);
v_index_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_index_465_);
lean_dec_ref_known(v___x_464_, 3);
v_size_466_ = lean_ctor_get(v_subst_461_, 0);
lean_inc(v_size_466_);
lean_inc(v_fvarId_373_);
v___x_467_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_461_, v_size_466_, v_index_465_, v_fvarId_373_, v___x_463_);
lean_dec(v_index_465_);
v_jpParamMask_407_ = v_jpParamMask_462_;
v___y_408_ = v___x_467_;
goto v___jp_406_;
}
case 1:
{
lean_object* v_index_468_; lean_object* v_size_469_; lean_object* v_keyArray_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v_index_468_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_index_468_);
lean_dec_ref_known(v___x_464_, 1);
v_size_469_ = lean_ctor_get(v_subst_461_, 0);
v_keyArray_470_ = lean_ctor_get(v_subst_461_, 1);
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_nat_add(v_size_469_, v___x_471_);
v___x_473_ = lean_array_get_size(v_keyArray_470_);
v___x_474_ = lean_nat_dec_lt(v___x_472_, v___x_473_);
if (v___x_474_ == 0)
{
lean_dec(v___x_472_);
lean_dec(v_index_468_);
lean_dec_ref(v_jpParamMask_462_);
v___y_425_ = v_subst_461_;
v___y_426_ = v___x_460_;
v___y_427_ = v___x_463_;
goto v___jp_424_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_475_ = lean_unsigned_to_nat(4u);
v___x_476_ = lean_nat_mul(v___x_472_, v___x_475_);
v___x_477_ = lean_unsigned_to_nat(3u);
v___x_478_ = lean_nat_mul(v___x_473_, v___x_477_);
v___x_479_ = lean_nat_dec_le(v___x_476_, v___x_478_);
lean_dec(v___x_478_);
lean_dec(v___x_476_);
if (v___x_479_ == 0)
{
lean_dec(v___x_472_);
lean_dec(v_index_468_);
lean_dec_ref(v_jpParamMask_462_);
v___y_425_ = v_subst_461_;
v___y_426_ = v___x_460_;
v___y_427_ = v___x_463_;
goto v___jp_424_;
}
else
{
lean_object* v___x_480_; 
lean_dec(v___x_460_);
lean_inc(v_fvarId_373_);
v___x_480_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_461_, v___x_472_, v_index_468_, v_fvarId_373_, v___x_463_);
lean_dec(v_index_468_);
v_jpParamMask_407_ = v_jpParamMask_462_;
v___y_408_ = v___x_480_;
goto v___jp_406_;
}
}
}
default: 
{
lean_object* v_size_481_; lean_object* v_keyArray_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
lean_dec_ref(v_jpParamMask_462_);
v_size_481_ = lean_ctor_get(v_subst_461_, 0);
v_keyArray_482_ = lean_ctor_get(v_subst_461_, 1);
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_size_481_, v___x_483_);
v___x_485_ = lean_array_get_size(v_keyArray_482_);
v___x_486_ = lean_nat_dec_lt(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec(v___x_484_);
v___x_487_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_461_);
lean_dec_ref(v_subst_461_);
v___y_447_ = v___x_460_;
v___y_448_ = v___x_463_;
v___y_449_ = v___x_487_;
goto v___jp_446_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_488_ = lean_unsigned_to_nat(4u);
v___x_489_ = lean_nat_mul(v___x_484_, v___x_488_);
lean_dec(v___x_484_);
v___x_490_ = lean_unsigned_to_nat(3u);
v___x_491_ = lean_nat_mul(v___x_485_, v___x_490_);
v___x_492_ = lean_nat_dec_le(v___x_489_, v___x_491_);
lean_dec(v___x_491_);
lean_dec(v___x_489_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
v___x_493_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_461_);
lean_dec_ref(v_subst_461_);
v___y_447_ = v___x_460_;
v___y_448_ = v___x_463_;
v___y_449_ = v___x_493_;
goto v___jp_446_;
}
else
{
v___y_447_ = v___x_460_;
v___y_448_ = v___x_463_;
v___y_449_ = v_subst_461_;
goto v___jp_446_;
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
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_del_object(v___x_378_);
lean_dec(v_binderName_374_);
lean_dec(v_fvarId_373_);
v_a_497_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_380_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_380_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg___boxed(lean_object* v_p_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_a_508_);
lean_dec(v_a_507_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(lean_object* v_p_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_513_, v_a_514_, v_a_516_, v_a_517_, v_a_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___boxed(lean_object* v_p_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(v_p_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(lean_object* v_00_u03b2_529_, lean_object* v_m_530_, lean_object* v_query_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_m_530_, v_query_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___boxed(lean_object* v_00_u03b2_533_, lean_object* v_m_534_, lean_object* v_query_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(v_00_u03b2_533_, v_m_534_, v_query_535_);
lean_dec(v_query_535_);
lean_dec_ref(v_m_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1(lean_object* v_00_u03b2_537_, lean_object* v_m_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_m_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___boxed(lean_object* v_00_u03b2_540_, lean_object* v_m_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1(v_00_u03b2_540_, v_m_541_);
lean_dec_ref(v_m_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(lean_object* v_00_u03b2_543_, lean_object* v_m_544_, lean_object* v_query_545_, lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_m_544_, v_query_545_, v_x_546_, v_x_547_, v_x_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___boxed(lean_object* v_00_u03b2_551_, lean_object* v_m_552_, lean_object* v_query_553_, lean_object* v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(v_00_u03b2_551_, v_m_552_, v_query_553_, v_x_554_, v_x_555_, v_x_556_, v_x_557_);
lean_dec(v_query_553_);
lean_dec_ref(v_m_552_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2(lean_object* v_00_u03b2_559_, lean_object* v_init_560_, lean_object* v_b_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2___redArg(v_init_560_, v_b_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2___boxed(lean_object* v_00_u03b2_563_, lean_object* v_init_564_, lean_object* v_b_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2(v_00_u03b2_563_, v_init_564_, v_b_565_);
lean_dec_ref(v_b_565_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_567_, lean_object* v_b_568_, lean_object* v_acc_569_, lean_object* v_i_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2_spec__3___redArg(v_b_568_, v_acc_569_, v_i_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_572_, lean_object* v_b_573_, lean_object* v_acc_574_, lean_object* v_i_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1_spec__2_spec__3(v_00_u03b2_572_, v_b_573_, v_acc_574_, v_i_575_);
lean_dec_ref(v_b_573_);
return v_res_576_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = lean_box(0);
v___x_581_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_582_ = l_Lean_Expr_const___override(v___x_581_, v___x_580_);
return v___x_582_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2);
v___x_584_ = lean_box(1);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___x_583_);
return v___x_585_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_box(0);
v___x_590_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5));
v___x_591_ = l_Lean_Expr_const___override(v___x_590_, v___x_589_);
return v___x_591_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_box(0);
v___x_596_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8));
v___x_597_ = l_Lean_Expr_const___override(v___x_596_, v___x_595_);
return v___x_597_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9);
v___x_599_ = lean_box(1);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_598_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(lean_object* v_base_601_, lean_object* v_ctorInfo_602_, lean_object* v_field_603_){
_start:
{
switch(lean_obj_tag(v_field_603_))
{
case 0:
{
lean_object* v___x_604_; 
lean_dec(v_base_601_);
v___x_604_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3);
return v___x_604_;
}
case 1:
{
lean_object* v_i_605_; lean_object* v_type_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_614_; 
v_i_605_ = lean_ctor_get(v_field_603_, 0);
v_type_606_ = lean_ctor_get(v_field_603_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_field_603_);
if (v_isSharedCheck_614_ == 0)
{
v___x_608_ = v_field_603_;
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_type_606_);
lean_inc(v_i_605_);
lean_dec(v_field_603_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set_tag(v___x_608_, 6);
lean_ctor_set(v___x_608_, 1, v_base_601_);
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_i_605_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_base_601_);
v___x_611_ = v_reuseFailAlloc_613_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v_type_606_);
return v___x_612_;
}
}
}
case 2:
{
lean_object* v_i_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_i_615_ = lean_ctor_get(v_field_603_, 0);
lean_inc(v_i_615_);
lean_dec_ref_known(v_field_603_, 1);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v_i_615_);
lean_ctor_set(v___x_616_, 1, v_base_601_);
v___x_617_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
return v___x_618_;
}
case 3:
{
lean_object* v_offset_619_; lean_object* v_type_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_631_; 
v_offset_619_ = lean_ctor_get(v_field_603_, 1);
v_type_620_ = lean_ctor_get(v_field_603_, 2);
v_isSharedCheck_631_ = !lean_is_exclusive(v_field_603_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v_field_603_, 0);
lean_dec(v_unused_632_);
v___x_622_ = v_field_603_;
v_isShared_623_ = v_isSharedCheck_631_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_type_620_);
lean_inc(v_offset_619_);
lean_dec(v_field_603_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_631_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_size_624_; lean_object* v_usize_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v_size_624_ = lean_ctor_get(v_ctorInfo_602_, 2);
v_usize_625_ = lean_ctor_get(v_ctorInfo_602_, 3);
v___x_626_ = lean_nat_add(v_size_624_, v_usize_625_);
if (v_isShared_623_ == 0)
{
lean_ctor_set_tag(v___x_622_, 8);
lean_ctor_set(v___x_622_, 2, v_base_601_);
lean_ctor_set(v___x_622_, 0, v___x_626_);
v___x_628_ = v___x_622_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_offset_619_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_base_601_);
v___x_628_ = v_reuseFailAlloc_630_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_type_620_);
return v___x_629_;
}
}
}
default: 
{
lean_object* v___x_633_; 
lean_dec(v_base_601_);
v___x_633_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10);
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___boxed(lean_object* v_base_634_, lean_object* v_ctorInfo_635_, lean_object* v_field_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_base_634_, v_ctorInfo_635_, v_field_636_);
lean_dec_ref(v_ctorInfo_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(lean_object* v_arg_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_641_; lean_object* v_subst_642_; uint8_t v___x_643_; uint8_t v___x_644_; lean_object* v___x_645_; 
v___x_641_ = lean_st_ref_get(v_a_639_);
v_subst_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc_ref(v_subst_642_);
lean_dec(v___x_641_);
v___x_643_ = 0;
v___x_644_ = 1;
v___x_645_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v___x_643_, v_subst_642_, v_arg_638_, v___x_644_);
lean_dec_ref(v_subst_642_);
if (lean_obj_tag(v___x_645_) == 1)
{
lean_object* v_fvarId_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_fvarId_646_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_654_ == 0)
{
v___x_648_ = v___x_645_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_fvarId_646_);
lean_dec(v___x_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
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
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fvarId_646_);
v___x_651_ = v_reuseFailAlloc_653_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec(v___x_645_);
v___x_655_ = lean_box(0);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg___boxed(lean_object* v_arg_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_657_, v_a_658_);
lean_dec(v_a_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(lean_object* v_arg_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_661_, v_a_662_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___boxed(lean_object* v_arg_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(v_arg_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(lean_object* v_msg_677_){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = l_Lean_instInhabitedExpr;
v___x_679_ = lean_panic_fn_borrowed(v___x_678_, v_msg_677_);
return v___x_679_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_683_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2));
v___x_684_ = lean_unsigned_to_nat(11u);
v___x_685_ = lean_unsigned_to_nat(83u);
v___x_686_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1));
v___x_687_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_688_ = l_mkPanicMessageWithDecl(v___x_687_, v___x_686_, v___x_685_, v___x_684_, v___x_683_);
return v___x_688_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_box(0);
v___x_690_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_691_ = l_Lean_mkConst(v___x_690_, v___x_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(lean_object* v_type_692_, lean_object* v_arity_693_){
_start:
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_nat_dec_eq(v_arity_693_, v___x_697_);
if (v___x_698_ == 0)
{
switch(lean_obj_tag(v_type_692_))
{
case 7:
{
lean_object* v_body_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_body_699_ = lean_ctor_get(v_type_692_, 2);
v___x_700_ = lean_unsigned_to_nat(1u);
v___x_701_ = lean_nat_sub(v_arity_693_, v___x_700_);
lean_dec(v_arity_693_);
v_type_692_ = v_body_699_;
v_arity_693_ = v___x_701_;
goto _start;
}
case 4:
{
lean_object* v_declName_703_; 
lean_dec(v_arity_693_);
v_declName_703_ = lean_ctor_get(v_type_692_, 0);
if (lean_obj_tag(v_declName_703_) == 1)
{
lean_object* v_pre_704_; 
v_pre_704_ = lean_ctor_get(v_declName_703_, 0);
if (lean_obj_tag(v_pre_704_) == 0)
{
lean_object* v_str_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_str_705_ = lean_ctor_get(v_declName_703_, 1);
v___x_706_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0));
v___x_707_ = lean_string_dec_eq(v_str_705_, v___x_706_);
if (v___x_707_ == 0)
{
goto v___jp_694_;
}
else
{
lean_object* v___x_708_; 
v___x_708_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4);
return v___x_708_;
}
}
else
{
goto v___jp_694_;
}
}
else
{
goto v___jp_694_;
}
}
default: 
{
lean_dec(v_arity_693_);
goto v___jp_694_;
}
}
}
else
{
lean_dec(v_arity_693_);
lean_inc_ref(v_type_692_);
return v_type_692_;
}
v___jp_694_:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3);
v___x_696_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(v___x_695_);
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___boxed(lean_object* v_type_709_, lean_object* v_arity_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_709_, v_arity_710_);
lean_dec_ref(v_type_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object* v_type_712_, lean_object* v_arity_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_712_, v_arity_713_);
v___x_718_ = l_Lean_Compiler_LCNF_toImpureType(v___x_717_, v_a_714_, v_a_715_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType___boxed(lean_object* v_type_719_, lean_object* v_arity_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_719_, v_arity_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec_ref(v_type_719_);
return v_res_724_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_728_ = lean_box(0);
v___x_729_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1));
v___x_730_ = l_Lean_Expr_const___override(v___x_729_, v___x_728_);
return v___x_730_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_box(0);
v___x_735_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4));
v___x_736_ = l_Lean_Expr_const___override(v___x_735_, v___x_734_);
return v___x_736_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_box(0);
v___x_741_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7));
v___x_742_ = l_Lean_Expr_const___override(v___x_741_, v___x_740_);
return v___x_742_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_box(0);
v___x_747_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10));
v___x_748_ = l_Lean_Expr_const___override(v___x_747_, v___x_746_);
return v___x_748_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_752_ = lean_box(0);
v___x_753_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13));
v___x_754_ = l_Lean_Expr_const___override(v___x_753_, v___x_752_);
return v___x_754_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_758_ = lean_box(0);
v___x_759_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16));
v___x_760_ = l_Lean_Expr_const___override(v___x_759_, v___x_758_);
return v___x_760_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = lean_box(0);
v___x_765_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19));
v___x_766_ = l_Lean_Expr_const___override(v___x_765_, v___x_764_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(lean_object* v_v_767_){
_start:
{
switch(lean_obj_tag(v_v_767_))
{
case 0:
{
lean_object* v_val_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v_val_768_ = lean_ctor_get(v_v_767_, 0);
v___x_769_ = lean_cstr_to_nat("4294967296");
v___x_770_ = lean_nat_dec_lt(v_val_768_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
v___x_771_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
return v___x_771_;
}
else
{
lean_object* v___x_772_; 
v___x_772_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
return v___x_772_;
}
}
case 1:
{
lean_object* v___x_773_; 
v___x_773_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
return v___x_773_;
}
case 2:
{
lean_object* v___x_774_; 
v___x_774_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11);
return v___x_774_;
}
case 3:
{
lean_object* v___x_775_; 
v___x_775_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14);
return v___x_775_;
}
case 4:
{
lean_object* v___x_776_; 
v___x_776_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17);
return v___x_776_;
}
case 5:
{
lean_object* v___x_777_; 
v___x_777_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20);
return v___x_777_;
}
default: 
{
lean_object* v___x_778_; 
v___x_778_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
return v___x_778_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___boxed(lean_object* v_v_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_v_779_);
lean_dec_ref(v_v_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(lean_object* v_as_781_, size_t v_i_782_, size_t v_stop_783_, lean_object* v_b_784_){
_start:
{
lean_object* v___y_786_; uint8_t v___x_790_; 
v___x_790_ = lean_usize_dec_eq(v_i_782_, v_stop_783_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v_snd_792_; uint8_t v___x_793_; 
v___x_791_ = lean_array_uget_borrowed(v_as_781_, v_i_782_);
v_snd_792_ = lean_ctor_get(v___x_791_, 1);
v___x_793_ = lean_unbox(v_snd_792_);
if (v___x_793_ == 0)
{
v___y_786_ = v_b_784_;
goto v___jp_785_;
}
else
{
lean_object* v_fst_794_; lean_object* v___x_795_; 
v_fst_794_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_fst_794_);
v___x_795_ = lean_array_push(v_b_784_, v_fst_794_);
v___y_786_ = v___x_795_;
goto v___jp_785_;
}
}
else
{
return v_b_784_;
}
v___jp_785_:
{
size_t v___x_787_; size_t v___x_788_; 
v___x_787_ = ((size_t)1ULL);
v___x_788_ = lean_usize_add(v_i_782_, v___x_787_);
v_i_782_ = v___x_788_;
v_b_784_ = v___y_786_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4___boxed(lean_object* v_as_796_, lean_object* v_i_797_, lean_object* v_stop_798_, lean_object* v_b_799_){
_start:
{
size_t v_i_boxed_800_; size_t v_stop_boxed_801_; lean_object* v_res_802_; 
v_i_boxed_800_ = lean_unbox_usize(v_i_797_);
lean_dec(v_i_797_);
v_stop_boxed_801_ = lean_unbox_usize(v_stop_798_);
lean_dec(v_stop_798_);
v_res_802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v_as_796_, v_i_boxed_800_, v_stop_boxed_801_, v_b_799_);
lean_dec_ref(v_as_796_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object* v_as_803_, size_t v_i_804_, size_t v_stop_805_, lean_object* v_b_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_a_810_; uint8_t v___x_814_; 
v___x_814_ = lean_usize_dec_eq(v_i_804_, v_stop_805_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v_snd_816_; uint8_t v___x_817_; 
v___x_815_ = lean_array_uget_borrowed(v_as_803_, v_i_804_);
v_snd_816_ = lean_ctor_get(v___x_815_, 1);
v___x_817_ = lean_unbox(v_snd_816_);
if (v___x_817_ == 0)
{
v_a_810_ = v_b_806_;
goto v___jp_809_;
}
else
{
lean_object* v_fst_818_; lean_object* v___x_819_; 
v_fst_818_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_fst_818_);
v___x_819_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_fst_818_, v___y_807_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_821_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
v___x_821_ = lean_array_push(v_b_806_, v_a_820_);
v_a_810_ = v___x_821_;
goto v___jp_809_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec_ref(v_b_806_);
v_a_822_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_819_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_819_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
else
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v_b_806_);
return v___x_830_;
}
v___jp_809_:
{
size_t v___x_811_; size_t v___x_812_; 
v___x_811_ = ((size_t)1ULL);
v___x_812_ = lean_usize_add(v_i_804_, v___x_811_);
v_i_804_ = v___x_812_;
v_b_806_ = v_a_810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object* v_as_831_, lean_object* v_i_832_, lean_object* v_stop_833_, lean_object* v_b_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
size_t v_i_boxed_837_; size_t v_stop_boxed_838_; lean_object* v_res_839_; 
v_i_boxed_837_ = lean_unbox_usize(v_i_832_);
lean_dec(v_i_832_);
v_stop_boxed_838_ = lean_unbox_usize(v_stop_833_);
lean_dec(v_stop_833_);
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_831_, v_i_boxed_837_, v_stop_boxed_838_, v_b_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v_as_831_);
return v_res_839_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0(void){
_start:
{
uint8_t v___x_840_; lean_object* v___x_841_; 
v___x_840_ = 1;
v___x_841_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(lean_object* v_msg_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; lean_object* v_toApplicative_850_; lean_object* v_toFunctor_851_; lean_object* v_toSeq_852_; lean_object* v_toSeqLeft_853_; lean_object* v_toSeqRight_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___f_857_; lean_object* v___f_858_; lean_object* v___x_859_; lean_object* v___f_860_; lean_object* v___f_861_; lean_object* v___f_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_toApplicative_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_898_; 
v___x_849_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_850_ = lean_ctor_get(v___x_849_, 0);
v_toFunctor_851_ = lean_ctor_get(v_toApplicative_850_, 0);
v_toSeq_852_ = lean_ctor_get(v_toApplicative_850_, 2);
v_toSeqLeft_853_ = lean_ctor_get(v_toApplicative_850_, 3);
v_toSeqRight_854_ = lean_ctor_get(v_toApplicative_850_, 4);
v___f_855_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_856_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref_n(v_toFunctor_851_, 2);
v___f_857_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_857_, 0, v_toFunctor_851_);
v___f_858_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_858_, 0, v_toFunctor_851_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___f_857_);
lean_ctor_set(v___x_859_, 1, v___f_858_);
lean_inc(v_toSeqRight_854_);
v___f_860_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_860_, 0, v_toSeqRight_854_);
lean_inc(v_toSeqLeft_853_);
v___f_861_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_861_, 0, v_toSeqLeft_853_);
lean_inc(v_toSeq_852_);
v___f_862_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_862_, 0, v_toSeq_852_);
v___x_863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_863_, 0, v___x_859_);
lean_ctor_set(v___x_863_, 1, v___f_855_);
lean_ctor_set(v___x_863_, 2, v___f_862_);
lean_ctor_set(v___x_863_, 3, v___f_861_);
lean_ctor_set(v___x_863_, 4, v___f_860_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___f_856_);
v___x_865_ = l_StateRefT_x27_instMonad___redArg(v___x_864_);
v_toApplicative_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v___x_865_, 1);
lean_dec(v_unused_899_);
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_898_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_toApplicative_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_898_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_toFunctor_870_; lean_object* v_toSeq_871_; lean_object* v_toSeqLeft_872_; lean_object* v_toSeqRight_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_896_; 
v_toFunctor_870_ = lean_ctor_get(v_toApplicative_866_, 0);
v_toSeq_871_ = lean_ctor_get(v_toApplicative_866_, 2);
v_toSeqLeft_872_ = lean_ctor_get(v_toApplicative_866_, 3);
v_toSeqRight_873_ = lean_ctor_get(v_toApplicative_866_, 4);
v_isSharedCheck_896_ = !lean_is_exclusive(v_toApplicative_866_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v_toApplicative_866_, 1);
lean_dec(v_unused_897_);
v___x_875_ = v_toApplicative_866_;
v_isShared_876_ = v_isSharedCheck_896_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_toSeqRight_873_);
lean_inc(v_toSeqLeft_872_);
lean_inc(v_toSeq_871_);
lean_inc(v_toFunctor_870_);
lean_dec(v_toApplicative_866_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_896_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___f_877_; lean_object* v___f_878_; lean_object* v___f_879_; lean_object* v___f_880_; lean_object* v___x_881_; lean_object* v___f_882_; lean_object* v___f_883_; lean_object* v___f_884_; lean_object* v___x_886_; 
v___f_877_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_878_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_870_);
v___f_879_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_879_, 0, v_toFunctor_870_);
v___f_880_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_880_, 0, v_toFunctor_870_);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v___f_879_);
lean_ctor_set(v___x_881_, 1, v___f_880_);
v___f_882_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_882_, 0, v_toSeqRight_873_);
v___f_883_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_883_, 0, v_toSeqLeft_872_);
v___f_884_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_884_, 0, v_toSeq_871_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v___f_882_);
lean_ctor_set(v___x_875_, 3, v___f_883_);
lean_ctor_set(v___x_875_, 2, v___f_884_);
lean_ctor_set(v___x_875_, 1, v___f_877_);
lean_ctor_set(v___x_875_, 0, v___x_881_);
v___x_886_ = v___x_875_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___f_877_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v___f_884_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v___f_883_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v___f_882_);
v___x_886_ = v_reuseFailAlloc_895_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___f_878_);
lean_ctor_set(v___x_868_, 0, v___x_886_);
v___x_888_ = v___x_868_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___f_878_);
v___x_888_ = v_reuseFailAlloc_894_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_55137__overap_892_; lean_object* v___x_893_; 
v___x_889_ = l_StateRefT_x27_instMonad___redArg(v___x_888_);
v___x_890_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0);
v___x_891_ = l_instInhabitedOfMonad___redArg(v___x_889_, v___x_890_);
v___x_55137__overap_892_ = lean_panic_fn_borrowed(v___x_891_, v_msg_842_);
lean_dec(v___x_891_);
lean_inc(v___y_847_);
lean_inc_ref(v___y_846_);
lean_inc(v___y_845_);
lean_inc_ref(v___y_844_);
lean_inc(v___y_843_);
v___x_893_ = lean_apply_6(v___x_55137__overap_892_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, lean_box(0));
return v___x_893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(lean_object* v_msg_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v_msg_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
return v_res_907_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0(void){
_start:
{
uint8_t v___x_908_; lean_object* v___x_909_; 
v___x_908_ = 0;
v___x_909_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(lean_object* v_upperBound_910_, lean_object* v_params_911_, lean_object* v___x_912_, lean_object* v_discr_913_, lean_object* v_a_914_, lean_object* v_b_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_a_919_; uint8_t v___x_923_; 
v___x_923_ = lean_nat_dec_lt(v_a_914_, v_upperBound_910_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; 
lean_dec(v_a_914_);
lean_dec(v_discr_913_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v_b_915_);
return v___x_924_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_925_ = lean_box(0);
v___x_926_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0);
v___x_927_ = lean_array_get_borrowed(v___x_926_, v_params_911_, v_a_914_);
v___x_928_ = lean_nat_dec_eq(v_a_914_, v___x_912_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v_fvarId_930_; lean_object* v_subst_931_; lean_object* v_jpParamMask_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_1007_; 
v___x_929_ = lean_st_ref_take(v___y_916_);
v_fvarId_930_ = lean_ctor_get(v___x_927_, 0);
v_subst_931_ = lean_ctor_get(v___x_929_, 0);
v_jpParamMask_932_ = lean_ctor_get(v___x_929_, 1);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_934_ = v___x_929_;
v_isShared_935_ = v_isSharedCheck_1007_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_jpParamMask_932_);
lean_inc(v_subst_931_);
lean_dec(v___x_929_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_1007_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___y_937_; lean_object* v___x_942_; lean_object* v___y_944_; lean_object* v_i_945_; lean_object* v___y_951_; lean_object* v___y_961_; lean_object* v_i_962_; lean_object* v___x_977_; 
v___x_942_ = lean_box(0);
v___x_977_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_931_, v_fvarId_930_);
switch(lean_obj_tag(v___x_977_))
{
case 0:
{
lean_object* v_index_978_; lean_object* v_size_979_; lean_object* v___x_980_; 
v_index_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_index_978_);
lean_dec_ref_known(v___x_977_, 3);
v_size_979_ = lean_ctor_get(v_subst_931_, 0);
lean_inc(v_size_979_);
lean_inc(v_fvarId_930_);
v___x_980_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_931_, v_size_979_, v_index_978_, v_fvarId_930_, v___x_942_);
lean_dec(v_index_978_);
v___y_937_ = v___x_980_;
goto v___jp_936_;
}
case 1:
{
lean_object* v_index_981_; lean_object* v_size_982_; lean_object* v_keyArray_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_index_981_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_index_981_);
lean_dec_ref_known(v___x_977_, 1);
v_size_982_ = lean_ctor_get(v_subst_931_, 0);
v_keyArray_983_ = lean_ctor_get(v_subst_931_, 1);
v___x_984_ = lean_unsigned_to_nat(1u);
v___x_985_ = lean_nat_add(v_size_982_, v___x_984_);
v___x_986_ = lean_array_get_size(v_keyArray_983_);
v___x_987_ = lean_nat_dec_lt(v___x_985_, v___x_986_);
if (v___x_987_ == 0)
{
lean_dec(v___x_985_);
lean_dec(v_index_981_);
goto v___jp_967_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_988_ = lean_unsigned_to_nat(4u);
v___x_989_ = lean_nat_mul(v___x_985_, v___x_988_);
v___x_990_ = lean_unsigned_to_nat(3u);
v___x_991_ = lean_nat_mul(v___x_986_, v___x_990_);
v___x_992_ = lean_nat_dec_le(v___x_989_, v___x_991_);
lean_dec(v___x_991_);
lean_dec(v___x_989_);
if (v___x_992_ == 0)
{
lean_dec(v___x_985_);
lean_dec(v_index_981_);
goto v___jp_967_;
}
else
{
lean_object* v___x_993_; 
lean_inc(v_fvarId_930_);
v___x_993_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_931_, v___x_985_, v_index_981_, v_fvarId_930_, v___x_942_);
lean_dec(v_index_981_);
v___y_937_ = v___x_993_;
goto v___jp_936_;
}
}
}
default: 
{
lean_object* v_size_994_; lean_object* v_keyArray_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v_size_994_ = lean_ctor_get(v_subst_931_, 0);
v_keyArray_995_ = lean_ctor_get(v_subst_931_, 1);
v___x_996_ = lean_unsigned_to_nat(1u);
v___x_997_ = lean_nat_add(v_size_994_, v___x_996_);
v___x_998_ = lean_array_get_size(v_keyArray_995_);
v___x_999_ = lean_nat_dec_lt(v___x_997_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
lean_dec(v___x_997_);
v___x_1000_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_931_);
lean_dec_ref(v_subst_931_);
v___y_951_ = v___x_1000_;
goto v___jp_950_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1001_ = lean_unsigned_to_nat(4u);
v___x_1002_ = lean_nat_mul(v___x_997_, v___x_1001_);
lean_dec(v___x_997_);
v___x_1003_ = lean_unsigned_to_nat(3u);
v___x_1004_ = lean_nat_mul(v___x_998_, v___x_1003_);
v___x_1005_ = lean_nat_dec_le(v___x_1002_, v___x_1004_);
lean_dec(v___x_1004_);
lean_dec(v___x_1002_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_931_);
lean_dec_ref(v_subst_931_);
v___y_951_ = v___x_1006_;
goto v___jp_950_;
}
else
{
v___y_951_ = v_subst_931_;
goto v___jp_950_;
}
}
}
}
v___jp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___y_937_);
v___x_939_ = v___x_934_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___y_937_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_jpParamMask_932_);
v___x_939_ = v_reuseFailAlloc_941_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; 
v___x_940_ = lean_st_ref_put(v___y_916_, v___x_939_);
v_a_919_ = v___x_925_;
goto v___jp_918_;
}
}
v___jp_943_:
{
lean_object* v_size_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_size_946_ = lean_ctor_get(v___y_944_, 0);
v___x_947_ = lean_unsigned_to_nat(1u);
v___x_948_ = lean_nat_add(v_size_946_, v___x_947_);
lean_inc(v_fvarId_930_);
v___x_949_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_944_, v___x_948_, v_i_945_, v_fvarId_930_, v___x_942_);
lean_dec(v_i_945_);
v___y_937_ = v___x_949_;
goto v___jp_936_;
}
v___jp_950_:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___y_951_, v_fvarId_930_);
switch(lean_obj_tag(v___x_952_))
{
case 0:
{
lean_object* v_index_953_; lean_object* v_size_954_; lean_object* v___x_955_; 
v_index_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_index_953_);
lean_dec_ref_known(v___x_952_, 3);
v_size_954_ = lean_ctor_get(v___y_951_, 0);
lean_inc(v_size_954_);
lean_inc(v_fvarId_930_);
v___x_955_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_951_, v_size_954_, v_index_953_, v_fvarId_930_, v___x_942_);
lean_dec(v_index_953_);
v___y_937_ = v___x_955_;
goto v___jp_936_;
}
case 1:
{
lean_object* v_index_956_; 
v_index_956_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_index_956_);
lean_dec_ref_known(v___x_952_, 1);
v___y_944_ = v___y_951_;
v_i_945_ = v_index_956_;
goto v___jp_943_;
}
default: 
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_951_, v___x_957_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_index_959_; 
v_index_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_index_959_);
lean_dec_ref_known(v___x_958_, 1);
v___y_944_ = v___y_951_;
v_i_945_ = v_index_959_;
goto v___jp_943_;
}
else
{
v___y_937_ = v___y_951_;
goto v___jp_936_;
}
}
}
}
v___jp_960_:
{
lean_object* v_size_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_size_963_ = lean_ctor_get(v___y_961_, 0);
v___x_964_ = lean_unsigned_to_nat(1u);
v___x_965_ = lean_nat_add(v_size_963_, v___x_964_);
lean_inc(v_fvarId_930_);
v___x_966_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_961_, v___x_965_, v_i_962_, v_fvarId_930_, v___x_942_);
lean_dec(v_i_962_);
v___y_937_ = v___x_966_;
goto v___jp_936_;
}
v___jp_967_:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_931_);
lean_dec_ref(v_subst_931_);
v___x_969_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___x_968_, v_fvarId_930_);
switch(lean_obj_tag(v___x_969_))
{
case 0:
{
lean_object* v_index_970_; lean_object* v_size_971_; lean_object* v___x_972_; 
v_index_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_index_970_);
lean_dec_ref_known(v___x_969_, 3);
v_size_971_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_size_971_);
lean_inc(v_fvarId_930_);
v___x_972_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_968_, v_size_971_, v_index_970_, v_fvarId_930_, v___x_942_);
lean_dec(v_index_970_);
v___y_937_ = v___x_972_;
goto v___jp_936_;
}
case 1:
{
lean_object* v_index_973_; 
v_index_973_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_index_973_);
lean_dec_ref_known(v___x_969_, 1);
v___y_961_ = v___x_968_;
v_i_962_ = v_index_973_;
goto v___jp_960_;
}
default: 
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_968_, v___x_974_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_index_976_; 
v_index_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_index_976_);
lean_dec_ref_known(v___x_975_, 1);
v___y_961_ = v___x_968_;
v_i_962_ = v_index_976_;
goto v___jp_960_;
}
else
{
v___y_937_ = v___x_968_;
goto v___jp_936_;
}
}
}
}
}
}
else
{
lean_object* v___x_1008_; lean_object* v_fvarId_1009_; lean_object* v_subst_1010_; lean_object* v_jpParamMask_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1086_; 
v___x_1008_ = lean_st_ref_take(v___y_916_);
v_fvarId_1009_ = lean_ctor_get(v___x_927_, 0);
v_subst_1010_ = lean_ctor_get(v___x_1008_, 0);
v_jpParamMask_1011_ = lean_ctor_get(v___x_1008_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1013_ = v___x_1008_;
v_isShared_1014_ = v_isSharedCheck_1086_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_jpParamMask_1011_);
lean_inc(v_subst_1010_);
lean_dec(v___x_1008_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1086_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___y_1016_; lean_object* v___x_1021_; lean_object* v___y_1023_; lean_object* v_i_1024_; lean_object* v___y_1030_; lean_object* v___y_1040_; lean_object* v_i_1041_; lean_object* v___x_1056_; 
lean_inc(v_discr_913_);
v___x_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1021_, 0, v_discr_913_);
v___x_1056_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1010_, v_fvarId_1009_);
switch(lean_obj_tag(v___x_1056_))
{
case 0:
{
lean_object* v_index_1057_; lean_object* v_size_1058_; lean_object* v___x_1059_; 
v_index_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_index_1057_);
lean_dec_ref_known(v___x_1056_, 3);
v_size_1058_ = lean_ctor_get(v_subst_1010_, 0);
lean_inc(v_size_1058_);
lean_inc(v_fvarId_1009_);
v___x_1059_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_1010_, v_size_1058_, v_index_1057_, v_fvarId_1009_, v___x_1021_);
lean_dec(v_index_1057_);
v___y_1016_ = v___x_1059_;
goto v___jp_1015_;
}
case 1:
{
lean_object* v_index_1060_; lean_object* v_size_1061_; lean_object* v_keyArray_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_index_1060_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_index_1060_);
lean_dec_ref_known(v___x_1056_, 1);
v_size_1061_ = lean_ctor_get(v_subst_1010_, 0);
v_keyArray_1062_ = lean_ctor_get(v_subst_1010_, 1);
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = lean_nat_add(v_size_1061_, v___x_1063_);
v___x_1065_ = lean_array_get_size(v_keyArray_1062_);
v___x_1066_ = lean_nat_dec_lt(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_dec(v___x_1064_);
lean_dec(v_index_1060_);
goto v___jp_1046_;
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1067_ = lean_unsigned_to_nat(4u);
v___x_1068_ = lean_nat_mul(v___x_1064_, v___x_1067_);
v___x_1069_ = lean_unsigned_to_nat(3u);
v___x_1070_ = lean_nat_mul(v___x_1065_, v___x_1069_);
v___x_1071_ = lean_nat_dec_le(v___x_1068_, v___x_1070_);
lean_dec(v___x_1070_);
lean_dec(v___x_1068_);
if (v___x_1071_ == 0)
{
lean_dec(v___x_1064_);
lean_dec(v_index_1060_);
goto v___jp_1046_;
}
else
{
lean_object* v___x_1072_; 
lean_inc(v_fvarId_1009_);
v___x_1072_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_1010_, v___x_1064_, v_index_1060_, v_fvarId_1009_, v___x_1021_);
lean_dec(v_index_1060_);
v___y_1016_ = v___x_1072_;
goto v___jp_1015_;
}
}
}
default: 
{
lean_object* v_size_1073_; lean_object* v_keyArray_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v_size_1073_ = lean_ctor_get(v_subst_1010_, 0);
v_keyArray_1074_ = lean_ctor_get(v_subst_1010_, 1);
v___x_1075_ = lean_unsigned_to_nat(1u);
v___x_1076_ = lean_nat_add(v_size_1073_, v___x_1075_);
v___x_1077_ = lean_array_get_size(v_keyArray_1074_);
v___x_1078_ = lean_nat_dec_lt(v___x_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_dec(v___x_1076_);
v___x_1079_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1010_);
lean_dec_ref(v_subst_1010_);
v___y_1030_ = v___x_1079_;
goto v___jp_1029_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1080_ = lean_unsigned_to_nat(4u);
v___x_1081_ = lean_nat_mul(v___x_1076_, v___x_1080_);
lean_dec(v___x_1076_);
v___x_1082_ = lean_unsigned_to_nat(3u);
v___x_1083_ = lean_nat_mul(v___x_1077_, v___x_1082_);
v___x_1084_ = lean_nat_dec_le(v___x_1081_, v___x_1083_);
lean_dec(v___x_1083_);
lean_dec(v___x_1081_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1010_);
lean_dec_ref(v_subst_1010_);
v___y_1030_ = v___x_1085_;
goto v___jp_1029_;
}
else
{
v___y_1030_ = v_subst_1010_;
goto v___jp_1029_;
}
}
}
}
v___jp_1015_:
{
lean_object* v___x_1018_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___y_1016_);
v___x_1018_ = v___x_1013_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___y_1016_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_jpParamMask_1011_);
v___x_1018_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_st_ref_put(v___y_916_, v___x_1018_);
v_a_919_ = v___x_925_;
goto v___jp_918_;
}
}
v___jp_1022_:
{
lean_object* v_size_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_size_1025_ = lean_ctor_get(v___y_1023_, 0);
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_nat_add(v_size_1025_, v___x_1026_);
lean_inc(v_fvarId_1009_);
v___x_1028_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1023_, v___x_1027_, v_i_1024_, v_fvarId_1009_, v___x_1021_);
lean_dec(v_i_1024_);
v___y_1016_ = v___x_1028_;
goto v___jp_1015_;
}
v___jp_1029_:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___y_1030_, v_fvarId_1009_);
switch(lean_obj_tag(v___x_1031_))
{
case 0:
{
lean_object* v_index_1032_; lean_object* v_size_1033_; lean_object* v___x_1034_; 
v_index_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_index_1032_);
lean_dec_ref_known(v___x_1031_, 3);
v_size_1033_ = lean_ctor_get(v___y_1030_, 0);
lean_inc(v_size_1033_);
lean_inc(v_fvarId_1009_);
v___x_1034_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1030_, v_size_1033_, v_index_1032_, v_fvarId_1009_, v___x_1021_);
lean_dec(v_index_1032_);
v___y_1016_ = v___x_1034_;
goto v___jp_1015_;
}
case 1:
{
lean_object* v_index_1035_; 
v_index_1035_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_index_1035_);
lean_dec_ref_known(v___x_1031_, 1);
v___y_1023_ = v___y_1030_;
v_i_1024_ = v_index_1035_;
goto v___jp_1022_;
}
default: 
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1030_, v___x_1036_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_index_1038_; 
v_index_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_index_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v___y_1023_ = v___y_1030_;
v_i_1024_ = v_index_1038_;
goto v___jp_1022_;
}
else
{
lean_dec_ref_known(v___x_1021_, 1);
v___y_1016_ = v___y_1030_;
goto v___jp_1015_;
}
}
}
}
v___jp_1039_:
{
lean_object* v_size_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v_size_1042_ = lean_ctor_get(v___y_1040_, 0);
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = lean_nat_add(v_size_1042_, v___x_1043_);
lean_inc(v_fvarId_1009_);
v___x_1045_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1040_, v___x_1044_, v_i_1041_, v_fvarId_1009_, v___x_1021_);
lean_dec(v_i_1041_);
v___y_1016_ = v___x_1045_;
goto v___jp_1015_;
}
v___jp_1046_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1010_);
lean_dec_ref(v_subst_1010_);
v___x_1048_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___x_1047_, v_fvarId_1009_);
switch(lean_obj_tag(v___x_1048_))
{
case 0:
{
lean_object* v_index_1049_; lean_object* v_size_1050_; lean_object* v___x_1051_; 
v_index_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_index_1049_);
lean_dec_ref_known(v___x_1048_, 3);
v_size_1050_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_size_1050_);
lean_inc(v_fvarId_1009_);
v___x_1051_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1047_, v_size_1050_, v_index_1049_, v_fvarId_1009_, v___x_1021_);
lean_dec(v_index_1049_);
v___y_1016_ = v___x_1051_;
goto v___jp_1015_;
}
case 1:
{
lean_object* v_index_1052_; 
v_index_1052_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_index_1052_);
lean_dec_ref_known(v___x_1048_, 1);
v___y_1040_ = v___x_1047_;
v_i_1041_ = v_index_1052_;
goto v___jp_1039_;
}
default: 
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1047_, v___x_1053_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_index_1055_; 
v_index_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_index_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v___y_1040_ = v___x_1047_;
v_i_1041_ = v_index_1055_;
goto v___jp_1039_;
}
else
{
lean_dec_ref_known(v___x_1021_, 1);
v___y_1016_ = v___x_1047_;
goto v___jp_1015_;
}
}
}
}
}
}
}
v___jp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = lean_nat_add(v_a_914_, v___x_920_);
lean_dec(v_a_914_);
v_a_914_ = v___x_921_;
v_b_915_ = v_a_919_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(lean_object* v_upperBound_1087_, lean_object* v_params_1088_, lean_object* v___x_1089_, lean_object* v_discr_1090_, lean_object* v_a_1091_, lean_object* v_b_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_1087_, v_params_1088_, v___x_1089_, v_discr_1090_, v_a_1091_, v_b_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec(v___x_1089_);
lean_dec_ref(v_params_1088_);
lean_dec(v_upperBound_1087_);
return v_res_1095_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1099_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1);
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
lean_ctor_set(v___x_1101_, 2, v___x_1100_);
lean_ctor_set(v___x_1101_, 3, v___x_1100_);
lean_ctor_set(v___x_1101_, 4, v___x_1099_);
lean_ctor_set(v___x_1101_, 5, v___x_1099_);
lean_ctor_set(v___x_1101_, 6, v___x_1099_);
lean_ctor_set(v___x_1101_, 7, v___x_1099_);
lean_ctor_set(v___x_1101_, 8, v___x_1099_);
lean_ctor_set(v___x_1101_, 9, v___x_1099_);
lean_ctor_set(v___x_1101_, 10, v___x_1099_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(lean_object* v_msg_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_options_1108_; lean_object* v_ref_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_options_1108_ = lean_ctor_get(v___y_1105_, 2);
v_ref_1109_ = lean_ctor_get(v___y_1105_, 5);
v___x_1110_ = lean_st_ref_get(v___y_1106_);
v___x_1111_ = lean_st_ref_get(v___y_1104_);
v___x_1112_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1103_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1135_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1135_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1135_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_env_1117_; lean_object* v_lctx_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1133_; 
v_env_1117_ = lean_ctor_get(v___x_1110_, 0);
lean_inc_ref(v_env_1117_);
lean_dec(v___x_1110_);
v_lctx_1118_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v___x_1111_, 1);
lean_dec(v_unused_1134_);
v___x_1120_ = v___x_1111_;
v_isShared_1121_ = v_isSharedCheck_1133_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_lctx_1118_);
lean_dec(v___x_1111_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1133_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1122_ = lean_unbox(v_a_1113_);
lean_dec(v_a_1113_);
v___x_1123_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1118_, v___x_1122_);
lean_dec_ref(v_lctx_1118_);
v___x_1124_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2);
lean_inc_ref(v_options_1108_);
v___x_1125_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1125_, 0, v_env_1117_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
lean_ctor_set(v___x_1125_, 2, v___x_1123_);
lean_ctor_set(v___x_1125_, 3, v_options_1108_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 3);
lean_ctor_set(v___x_1120_, 1, v_msg_1102_);
lean_ctor_set(v___x_1120_, 0, v___x_1125_);
v___x_1127_ = v___x_1120_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_msg_1102_);
v___x_1127_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
lean_inc(v_ref_1109_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_ref_1109_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set_tag(v___x_1115_, 1);
lean_ctor_set(v___x_1115_, 0, v___x_1128_);
v___x_1130_ = v___x_1115_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v___x_1111_);
lean_dec(v___x_1110_);
lean_dec_ref(v_msg_1102_);
v_a_1136_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1112_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1112_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(lean_object* v_msg_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(size_t v_sz_1151_, size_t v_i_1152_, lean_object* v_bs_1153_, lean_object* v___y_1154_){
_start:
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_usize_dec_lt(v_i_1152_, v_sz_1151_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_bs_1153_);
return v___x_1157_;
}
else
{
lean_object* v_v_1158_; lean_object* v___x_1159_; 
v_v_1158_ = lean_array_uget_borrowed(v_bs_1153_, v_i_1152_);
lean_inc(v_v_1158_);
v___x_1159_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_v_1158_, v___y_1154_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1161_; lean_object* v_bs_x27_1162_; size_t v___x_1163_; size_t v___x_1164_; lean_object* v___x_1165_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1159_, 1);
v___x_1161_ = lean_unsigned_to_nat(0u);
v_bs_x27_1162_ = lean_array_uset(v_bs_1153_, v_i_1152_, v___x_1161_);
v___x_1163_ = ((size_t)1ULL);
v___x_1164_ = lean_usize_add(v_i_1152_, v___x_1163_);
v___x_1165_ = lean_array_uset(v_bs_x27_1162_, v_i_1152_, v_a_1160_);
v_i_1152_ = v___x_1164_;
v_bs_1153_ = v___x_1165_;
goto _start;
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec_ref(v_bs_1153_);
v_a_1167_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1159_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1159_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg___boxed(lean_object* v_sz_1175_, lean_object* v_i_1176_, lean_object* v_bs_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
size_t v_sz_boxed_1180_; size_t v_i_boxed_1181_; lean_object* v_res_1182_; 
v_sz_boxed_1180_ = lean_unbox_usize(v_sz_1175_);
lean_dec(v_sz_1175_);
v_i_boxed_1181_ = lean_unbox_usize(v_i_1176_);
lean_dec(v_i_1176_);
v_res_1182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_boxed_1180_, v_i_boxed_1181_, v_bs_1177_, v___y_1178_);
lean_dec(v___y_1178_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(lean_object* v_upperBound_1183_, lean_object* v_fieldInfo_1184_, lean_object* v___x_1185_, lean_object* v_a_1186_, lean_object* v_b_1187_){
_start:
{
lean_object* v_a_1190_; uint8_t v___x_1194_; 
v___x_1194_ = lean_nat_dec_lt(v_a_1186_, v_upperBound_1183_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
lean_dec(v_a_1186_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_b_1187_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_array_fget_borrowed(v_fieldInfo_1184_, v_a_1186_);
switch(lean_obj_tag(v___x_1196_))
{
case 1:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = lean_box(0);
v___x_1198_ = lean_array_get_borrowed(v___x_1197_, v___x_1185_, v_a_1186_);
lean_inc(v___x_1198_);
v___x_1199_ = lean_array_push(v_b_1187_, v___x_1198_);
v_a_1190_ = v___x_1199_;
goto v___jp_1189_;
}
case 2:
{
v_a_1190_ = v_b_1187_;
goto v___jp_1189_;
}
case 3:
{
v_a_1190_ = v_b_1187_;
goto v___jp_1189_;
}
default: 
{
v_a_1190_ = v_b_1187_;
goto v___jp_1189_;
}
}
}
v___jp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_nat_add(v_a_1186_, v___x_1191_);
lean_dec(v_a_1186_);
v_a_1186_ = v___x_1192_;
v_b_1187_ = v_a_1190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(lean_object* v_upperBound_1200_, lean_object* v_fieldInfo_1201_, lean_object* v___x_1202_, lean_object* v_a_1203_, lean_object* v_b_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_1200_, v_fieldInfo_1201_, v___x_1202_, v_a_1203_, v_b_1204_);
lean_dec_ref(v___x_1202_);
lean_dec_ref(v_fieldInfo_1201_);
lean_dec(v_upperBound_1200_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(size_t v_sz_1207_, size_t v_i_1208_, lean_object* v_bs_1209_){
_start:
{
uint8_t v___x_1210_; 
v___x_1210_ = lean_usize_dec_lt(v_i_1208_, v_sz_1207_);
if (v___x_1210_ == 0)
{
return v_bs_1209_;
}
else
{
lean_object* v_v_1211_; lean_object* v_type_1212_; lean_object* v___x_1213_; lean_object* v_bs_x27_1214_; uint8_t v___y_1216_; uint8_t v___y_1223_; uint8_t v___x_1225_; 
v_v_1211_ = lean_array_uget_borrowed(v_bs_1209_, v_i_1208_);
v_type_1212_ = lean_ctor_get(v_v_1211_, 2);
lean_inc_ref(v_type_1212_);
v___x_1213_ = lean_unsigned_to_nat(0u);
v_bs_x27_1214_ = lean_array_uset(v_bs_1209_, v_i_1208_, v___x_1213_);
v___x_1225_ = l_Lean_Expr_isVoid(v_type_1212_);
if (v___x_1225_ == 0)
{
uint8_t v___x_1226_; 
v___x_1226_ = l_Lean_Expr_isErased(v_type_1212_);
lean_dec_ref(v_type_1212_);
v___y_1223_ = v___x_1226_;
goto v___jp_1222_;
}
else
{
lean_dec_ref(v_type_1212_);
v___y_1223_ = v___x_1225_;
goto v___jp_1222_;
}
v___jp_1215_:
{
size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_i_1208_, v___x_1217_);
v___x_1219_ = lean_box(v___y_1216_);
v___x_1220_ = lean_array_uset(v_bs_x27_1214_, v_i_1208_, v___x_1219_);
v_i_1208_ = v___x_1218_;
v_bs_1209_ = v___x_1220_;
goto _start;
}
v___jp_1222_:
{
if (v___y_1223_ == 0)
{
v___y_1216_ = v___x_1210_;
goto v___jp_1215_;
}
else
{
uint8_t v___x_1224_; 
v___x_1224_ = 0;
v___y_1216_ = v___x_1224_;
goto v___jp_1215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object* v_sz_1227_, lean_object* v_i_1228_, lean_object* v_bs_1229_){
_start:
{
size_t v_sz_boxed_1230_; size_t v_i_boxed_1231_; lean_object* v_res_1232_; 
v_sz_boxed_1230_ = lean_unbox_usize(v_sz_1227_);
lean_dec(v_sz_1227_);
v_i_boxed_1231_ = lean_unbox_usize(v_i_1228_);
lean_dec(v_i_1228_);
v_res_1232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_boxed_1230_, v_i_boxed_1231_, v_bs_1229_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(size_t v_sz_1233_, size_t v_i_1234_, lean_object* v_bs_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v___x_1241_; 
v___x_1241_ = lean_usize_dec_lt(v_i_1234_, v_sz_1233_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v_bs_1235_);
return v___x_1242_;
}
else
{
lean_object* v_v_1243_; lean_object* v___x_1244_; 
v_v_1243_ = lean_array_uget_borrowed(v_bs_1235_, v_i_1234_);
lean_inc(v_v_1243_);
v___x_1244_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_v_1243_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; lean_object* v_bs_x27_1247_; size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1246_ = lean_unsigned_to_nat(0u);
v_bs_x27_1247_ = lean_array_uset(v_bs_1235_, v_i_1234_, v___x_1246_);
v___x_1248_ = ((size_t)1ULL);
v___x_1249_ = lean_usize_add(v_i_1234_, v___x_1248_);
v___x_1250_ = lean_array_uset(v_bs_x27_1247_, v_i_1234_, v_a_1245_);
v_i_1234_ = v___x_1249_;
v_bs_1235_ = v___x_1250_;
goto _start;
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v_bs_1235_);
v_a_1252_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1244_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1244_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(lean_object* v_sz_1260_, lean_object* v_i_1261_, lean_object* v_bs_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
size_t v_sz_boxed_1268_; size_t v_i_boxed_1269_; lean_object* v_res_1270_; 
v_sz_boxed_1268_ = lean_unbox_usize(v_sz_1260_);
lean_dec(v_sz_1260_);
v_i_boxed_1269_ = lean_unbox_usize(v_i_1261_);
lean_dec(v_i_1261_);
v_res_1270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_boxed_1268_, v_i_boxed_1269_, v_bs_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec(v___y_1263_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___redArg(lean_object* v_m_1271_, lean_object* v_query_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_m_1271_, v_query_1272_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_index_1274_; lean_object* v_key_1275_; lean_object* v_value_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
v_index_1274_ = lean_ctor_get(v___x_1273_, 0);
v_key_1275_ = lean_ctor_get(v___x_1273_, 1);
v_value_1276_ = lean_ctor_get(v___x_1273_, 2);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1273_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_value_1276_);
lean_inc(v_key_1275_);
lean_inc(v_index_1274_);
lean_dec(v___x_1273_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_index_1274_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_key_1275_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_value_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
lean_object* v___x_1284_; 
lean_dec(v___x_1273_);
v___x_1284_ = lean_box(1);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___redArg___boxed(lean_object* v_m_1285_, lean_object* v_query_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___redArg(v_m_1285_, v_query_1286_);
lean_dec(v_query_1286_);
lean_dec_ref(v_m_1285_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg(lean_object* v_m_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___redArg(v_m_1288_, v_a_1289_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_value_1291_; lean_object* v___x_1292_; 
v_value_1291_ = lean_ctor_get(v___x_1290_, 2);
lean_inc(v_value_1291_);
lean_dec_ref_known(v___x_1290_, 3);
v___x_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1292_, 0, v_value_1291_);
return v___x_1292_;
}
else
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_box(0);
return v___x_1293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg___boxed(lean_object* v_m_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg(v_m_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_m_1294_);
return v_res_1296_;
}
}
static lean_object* _init_l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__14___closed__0(void){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Array_instInhabited(lean_box(0));
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__14(lean_object* v_msg_1298_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_obj_once(&l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__14___closed__0, &l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__14___closed__0_once, _init_l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__14___closed__0);
v___x_1300_ = lean_panic_fn_borrowed(v___x_1299_, v_msg_1298_);
return v___x_1300_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1304_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__2));
v___x_1305_ = lean_unsigned_to_nat(12u);
v___x_1306_ = lean_unsigned_to_nat(672u);
v___x_1307_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__1));
v___x_1308_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__0));
v___x_1309_ = l_mkPanicMessageWithDecl(v___x_1308_, v___x_1307_, v___x_1306_, v___x_1305_, v___x_1304_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(lean_object* v_m_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg(v_m_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___closed__3);
v___x_1314_ = l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__14(v___x_1313_);
return v___x_1314_;
}
else
{
lean_object* v_val_1315_; 
v_val_1315_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_val_1315_);
lean_dec_ref_known(v___x_1312_, 1);
return v_val_1315_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(lean_object* v_m_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_m_1316_, v_a_1317_);
lean_dec(v_a_1317_);
lean_dec_ref(v_m_1316_);
return v_res_1318_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1321_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1));
v___x_1322_ = lean_unsigned_to_nat(12u);
v___x_1323_ = lean_unsigned_to_nat(116u);
v___x_1324_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1325_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1326_ = l_mkPanicMessageWithDecl(v___x_1325_, v___x_1324_, v___x_1323_, v___x_1322_, v___x_1321_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(lean_object* v_k_1327_, lean_object* v_decl_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v___x_1335_; lean_object* v_lctx_1336_; lean_object* v_nextIdx_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1357_; 
v___x_1335_ = lean_st_ref_take(v_a_1331_);
v_lctx_1336_ = lean_ctor_get(v___x_1335_, 0);
v_nextIdx_1337_ = lean_ctor_get(v___x_1335_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1339_ = v___x_1335_;
v_isShared_1340_ = v_isSharedCheck_1357_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_nextIdx_1337_);
lean_inc(v_lctx_1336_);
lean_dec(v___x_1335_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1357_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1341_ = 1;
lean_inc_ref(v_decl_1328_);
v___x_1342_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1341_, v_lctx_1336_, v_decl_1328_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1342_);
v___x_1344_ = v___x_1339_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_nextIdx_1337_);
v___x_1344_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_st_ref_put(v_a_1331_, v___x_1344_);
v___x_1346_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1327_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1355_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1355_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1355_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_decl_1328_);
lean_ctor_set(v___x_1351_, 1, v_a_1347_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1351_);
v___x_1353_ = v___x_1349_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
else
{
lean_dec_ref(v_decl_1328_);
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(lean_object* v_k_1358_, lean_object* v_fvarId_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v___x_1366_; lean_object* v_subst_1367_; lean_object* v_jpParamMask_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1444_; 
v___x_1366_ = lean_st_ref_take(v_a_1360_);
v_subst_1367_ = lean_ctor_get(v___x_1366_, 0);
v_jpParamMask_1368_ = lean_ctor_get(v___x_1366_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1370_ = v___x_1366_;
v_isShared_1371_ = v_isSharedCheck_1444_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_jpParamMask_1368_);
lean_inc(v_subst_1367_);
lean_dec(v___x_1366_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1444_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___y_1373_; lean_object* v___x_1379_; lean_object* v___y_1381_; lean_object* v_i_1382_; lean_object* v___y_1388_; lean_object* v___y_1398_; lean_object* v_i_1399_; lean_object* v___x_1414_; 
v___x_1379_ = lean_box(0);
v___x_1414_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1367_, v_fvarId_1359_);
switch(lean_obj_tag(v___x_1414_))
{
case 0:
{
lean_object* v_index_1415_; lean_object* v_size_1416_; lean_object* v___x_1417_; 
v_index_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_index_1415_);
lean_dec_ref_known(v___x_1414_, 3);
v_size_1416_ = lean_ctor_get(v_subst_1367_, 0);
lean_inc(v_size_1416_);
v___x_1417_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_1367_, v_size_1416_, v_index_1415_, v_fvarId_1359_, v___x_1379_);
lean_dec(v_index_1415_);
v___y_1373_ = v___x_1417_;
goto v___jp_1372_;
}
case 1:
{
lean_object* v_index_1418_; lean_object* v_size_1419_; lean_object* v_keyArray_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v_index_1418_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_index_1418_);
lean_dec_ref_known(v___x_1414_, 1);
v_size_1419_ = lean_ctor_get(v_subst_1367_, 0);
v_keyArray_1420_ = lean_ctor_get(v_subst_1367_, 1);
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = lean_nat_add(v_size_1419_, v___x_1421_);
v___x_1423_ = lean_array_get_size(v_keyArray_1420_);
v___x_1424_ = lean_nat_dec_lt(v___x_1422_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_dec(v___x_1422_);
lean_dec(v_index_1418_);
goto v___jp_1404_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1425_ = lean_unsigned_to_nat(4u);
v___x_1426_ = lean_nat_mul(v___x_1422_, v___x_1425_);
v___x_1427_ = lean_unsigned_to_nat(3u);
v___x_1428_ = lean_nat_mul(v___x_1423_, v___x_1427_);
v___x_1429_ = lean_nat_dec_le(v___x_1426_, v___x_1428_);
lean_dec(v___x_1428_);
lean_dec(v___x_1426_);
if (v___x_1429_ == 0)
{
lean_dec(v___x_1422_);
lean_dec(v_index_1418_);
goto v___jp_1404_;
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_1367_, v___x_1422_, v_index_1418_, v_fvarId_1359_, v___x_1379_);
lean_dec(v_index_1418_);
v___y_1373_ = v___x_1430_;
goto v___jp_1372_;
}
}
}
default: 
{
lean_object* v_size_1431_; lean_object* v_keyArray_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v_size_1431_ = lean_ctor_get(v_subst_1367_, 0);
v_keyArray_1432_ = lean_ctor_get(v_subst_1367_, 1);
v___x_1433_ = lean_unsigned_to_nat(1u);
v___x_1434_ = lean_nat_add(v_size_1431_, v___x_1433_);
v___x_1435_ = lean_array_get_size(v_keyArray_1432_);
v___x_1436_ = lean_nat_dec_lt(v___x_1434_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; 
lean_dec(v___x_1434_);
v___x_1437_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1367_);
lean_dec_ref(v_subst_1367_);
v___y_1388_ = v___x_1437_;
goto v___jp_1387_;
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1438_ = lean_unsigned_to_nat(4u);
v___x_1439_ = lean_nat_mul(v___x_1434_, v___x_1438_);
lean_dec(v___x_1434_);
v___x_1440_ = lean_unsigned_to_nat(3u);
v___x_1441_ = lean_nat_mul(v___x_1435_, v___x_1440_);
v___x_1442_ = lean_nat_dec_le(v___x_1439_, v___x_1441_);
lean_dec(v___x_1441_);
lean_dec(v___x_1439_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1367_);
lean_dec_ref(v_subst_1367_);
v___y_1388_ = v___x_1443_;
goto v___jp_1387_;
}
else
{
v___y_1388_ = v_subst_1367_;
goto v___jp_1387_;
}
}
}
}
v___jp_1372_:
{
lean_object* v___x_1375_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___y_1373_);
v___x_1375_ = v___x_1370_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___y_1373_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_jpParamMask_1368_);
v___x_1375_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_st_ref_put(v_a_1360_, v___x_1375_);
v___x_1377_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1358_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
return v___x_1377_;
}
}
v___jp_1380_:
{
lean_object* v_size_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_size_1383_ = lean_ctor_get(v___y_1381_, 0);
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_add(v_size_1383_, v___x_1384_);
v___x_1386_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1381_, v___x_1385_, v_i_1382_, v_fvarId_1359_, v___x_1379_);
lean_dec(v_i_1382_);
v___y_1373_ = v___x_1386_;
goto v___jp_1372_;
}
v___jp_1387_:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___y_1388_, v_fvarId_1359_);
switch(lean_obj_tag(v___x_1389_))
{
case 0:
{
lean_object* v_index_1390_; lean_object* v_size_1391_; lean_object* v___x_1392_; 
v_index_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_index_1390_);
lean_dec_ref_known(v___x_1389_, 3);
v_size_1391_ = lean_ctor_get(v___y_1388_, 0);
lean_inc(v_size_1391_);
v___x_1392_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1388_, v_size_1391_, v_index_1390_, v_fvarId_1359_, v___x_1379_);
lean_dec(v_index_1390_);
v___y_1373_ = v___x_1392_;
goto v___jp_1372_;
}
case 1:
{
lean_object* v_index_1393_; 
v_index_1393_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_index_1393_);
lean_dec_ref_known(v___x_1389_, 1);
v___y_1381_ = v___y_1388_;
v_i_1382_ = v_index_1393_;
goto v___jp_1380_;
}
default: 
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1395_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1388_, v___x_1394_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_index_1396_; 
v_index_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_index_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___y_1381_ = v___y_1388_;
v_i_1382_ = v_index_1396_;
goto v___jp_1380_;
}
else
{
lean_dec(v_fvarId_1359_);
v___y_1373_ = v___y_1388_;
goto v___jp_1372_;
}
}
}
}
v___jp_1397_:
{
lean_object* v_size_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_size_1400_ = lean_ctor_get(v___y_1398_, 0);
v___x_1401_ = lean_unsigned_to_nat(1u);
v___x_1402_ = lean_nat_add(v_size_1400_, v___x_1401_);
v___x_1403_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1398_, v___x_1402_, v_i_1399_, v_fvarId_1359_, v___x_1379_);
lean_dec(v_i_1399_);
v___y_1373_ = v___x_1403_;
goto v___jp_1372_;
}
v___jp_1404_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1367_);
lean_dec_ref(v_subst_1367_);
v___x_1406_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___x_1405_, v_fvarId_1359_);
switch(lean_obj_tag(v___x_1406_))
{
case 0:
{
lean_object* v_index_1407_; lean_object* v_size_1408_; lean_object* v___x_1409_; 
v_index_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_index_1407_);
lean_dec_ref_known(v___x_1406_, 3);
v_size_1408_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_size_1408_);
v___x_1409_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1405_, v_size_1408_, v_index_1407_, v_fvarId_1359_, v___x_1379_);
lean_dec(v_index_1407_);
v___y_1373_ = v___x_1409_;
goto v___jp_1372_;
}
case 1:
{
lean_object* v_index_1410_; 
v_index_1410_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_index_1410_);
lean_dec_ref_known(v___x_1406_, 1);
v___y_1398_ = v___x_1405_;
v_i_1399_ = v_index_1410_;
goto v___jp_1397_;
}
default: 
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1405_, v___x_1411_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_index_1413_; 
v_index_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_index_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___y_1398_ = v___x_1405_;
v_i_1399_ = v_index_1413_;
goto v___jp_1397_;
}
else
{
lean_dec(v_fvarId_1359_);
v___y_1373_ = v___x_1405_;
goto v___jp_1372_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(lean_object* v_decl_1446_, lean_object* v_k_1447_, lean_object* v_name_1448_, lean_object* v_numParams_1449_, lean_object* v_args_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v_fvarId_1457_; lean_object* v_binderName_1458_; lean_object* v_type_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1521_; 
v_fvarId_1457_ = lean_ctor_get(v_decl_1446_, 0);
v_binderName_1458_ = lean_ctor_get(v_decl_1446_, 1);
v_type_1459_ = lean_ctor_get(v_decl_1446_, 2);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_decl_1446_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; 
v_unused_1522_ = lean_ctor_get(v_decl_1446_, 3);
lean_dec(v_unused_1522_);
v___x_1461_ = v_decl_1446_;
v_isShared_1462_ = v_isSharedCheck_1521_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_type_1459_);
lean_inc(v_binderName_1458_);
lean_inc(v_fvarId_1457_);
lean_dec(v_decl_1446_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1521_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1459_, v_a_1454_, v_a_1455_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1449_);
v___x_1466_ = l_Array_extract___redArg(v_args_1450_, v___x_1465_, v_numParams_1449_);
v___x_1467_ = 1;
v___x_1468_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0));
lean_inc(v_binderName_1458_);
v___x_1469_ = l_Lean_Name_str___override(v_binderName_1458_, v___x_1468_);
v___x_1470_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1471_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1471_, 0, v_name_1448_);
lean_ctor_set(v___x_1471_, 1, v___x_1466_);
v___x_1472_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1467_, v___x_1469_, v___x_1470_, v___x_1471_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v_fvarId_1474_; lean_object* v___x_1475_; lean_object* v_lctx_1476_; lean_object* v_nextIdx_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1504_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v_fvarId_1474_ = lean_ctor_get(v_a_1473_, 0);
v___x_1475_ = lean_st_ref_take(v_a_1453_);
v_lctx_1476_ = lean_ctor_get(v___x_1475_, 0);
v_nextIdx_1477_ = lean_ctor_get(v___x_1475_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1479_ = v___x_1475_;
v_isShared_1480_ = v_isSharedCheck_1504_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_nextIdx_1477_);
lean_inc(v_lctx_1476_);
lean_dec(v___x_1475_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1504_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1481_ = lean_array_get_size(v_args_1450_);
v___x_1482_ = l_Array_extract___redArg(v_args_1450_, v_numParams_1449_, v___x_1481_);
lean_inc(v_fvarId_1474_);
v___x_1483_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1483_, 0, v_fvarId_1474_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1464_);
lean_dec(v_a_1464_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 3, v___x_1483_);
lean_ctor_set(v___x_1461_, 2, v___x_1484_);
v___x_1486_ = v___x_1461_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_fvarId_1457_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_binderName_1458_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v___x_1483_);
v___x_1486_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
lean_inc_ref(v___x_1486_);
v___x_1487_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1467_, v_lctx_1476_, v___x_1486_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1487_);
v___x_1489_ = v___x_1479_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_nextIdx_1477_);
v___x_1489_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_st_ref_put(v_a_1453_, v___x_1489_);
v___x_1491_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1447_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1501_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1501_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1501_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1486_);
lean_ctor_set(v___x_1496_, 1, v_a_1492_);
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v_a_1473_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1497_);
v___x_1499_ = v___x_1494_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
else
{
lean_dec_ref(v___x_1486_);
lean_dec(v_a_1473_);
return v___x_1491_;
}
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_a_1464_);
lean_del_object(v___x_1461_);
lean_dec(v_binderName_1458_);
lean_dec(v_fvarId_1457_);
lean_dec(v_numParams_1449_);
lean_dec_ref(v_k_1447_);
v_a_1505_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1472_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1472_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_del_object(v___x_1461_);
lean_dec(v_binderName_1458_);
lean_dec(v_fvarId_1457_);
lean_dec(v_numParams_1449_);
lean_dec(v_name_1448_);
lean_dec_ref(v_k_1447_);
v_a_1513_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1463_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1463_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(lean_object* v_decl_1523_, lean_object* v_k_1524_, lean_object* v_name_1525_, lean_object* v_args_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_fvarId_1533_; lean_object* v_binderName_1534_; lean_object* v_type_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1554_; 
v_fvarId_1533_ = lean_ctor_get(v_decl_1523_, 0);
v_binderName_1534_ = lean_ctor_get(v_decl_1523_, 1);
v_type_1535_ = lean_ctor_get(v_decl_1523_, 2);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_decl_1523_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v_decl_1523_, 3);
lean_dec(v_unused_1555_);
v___x_1537_ = v_decl_1523_;
v_isShared_1538_ = v_isSharedCheck_1554_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_type_1535_);
lean_inc(v_binderName_1534_);
lean_inc(v_fvarId_1533_);
lean_dec(v_decl_1523_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1554_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1535_, v_a_1530_, v_a_1531_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
v___x_1541_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_name_1525_);
lean_ctor_set(v___x_1541_, 1, v_args_1526_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 3, v___x_1541_);
lean_ctor_set(v___x_1537_, 2, v_a_1540_);
v___x_1543_ = v___x_1537_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_fvarId_1533_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_binderName_1534_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_a_1540_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1544_; 
v___x_1544_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1524_, v___x_1543_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_);
return v___x_1544_;
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_del_object(v___x_1537_);
lean_dec(v_binderName_1534_);
lean_dec(v_fvarId_1533_);
lean_dec_ref(v_args_1526_);
lean_dec(v_name_1525_);
lean_dec_ref(v_k_1524_);
v_a_1546_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1539_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1539_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(lean_object* v_decl_1556_, lean_object* v_k_1557_, lean_object* v_name_1558_, lean_object* v_args_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_fvarId_1566_; lean_object* v_binderName_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1577_; 
v_fvarId_1566_ = lean_ctor_get(v_decl_1556_, 0);
v_binderName_1567_ = lean_ctor_get(v_decl_1556_, 1);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_decl_1556_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; lean_object* v_unused_1579_; 
v_unused_1578_ = lean_ctor_get(v_decl_1556_, 3);
lean_dec(v_unused_1578_);
v_unused_1579_ = lean_ctor_get(v_decl_1556_, 2);
lean_dec(v_unused_1579_);
v___x_1569_ = v_decl_1556_;
v_isShared_1570_ = v_isSharedCheck_1577_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_binderName_1567_);
lean_inc(v_fvarId_1566_);
lean_dec(v_decl_1556_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1577_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1571_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1572_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_name_1558_);
lean_ctor_set(v___x_1572_, 1, v_args_1559_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 3, v___x_1572_);
lean_ctor_set(v___x_1569_, 2, v___x_1571_);
v___x_1574_ = v___x_1569_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_fvarId_1566_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_binderName_1567_);
lean_ctor_set(v_reuseFailAlloc_1576_, 2, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1576_, 3, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; 
v___x_1575_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1557_, v___x_1574_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
return v___x_1575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(lean_object* v_decl_1580_, lean_object* v_k_1581_, lean_object* v_name_1582_, lean_object* v_numParams_1583_, lean_object* v_args_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v_numArgs_1591_; uint8_t v___x_1592_; 
v_numArgs_1591_ = lean_array_get_size(v_args_1584_);
v___x_1592_ = lean_nat_dec_lt(v_numArgs_1591_, v_numParams_1583_);
if (v___x_1592_ == 0)
{
uint8_t v___x_1593_; 
v___x_1593_ = lean_nat_dec_eq(v_numArgs_1591_, v_numParams_1583_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_1580_, v_k_1581_, v_name_1582_, v_numParams_1583_, v_args_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec_ref(v_args_1584_);
return v___x_1594_;
}
else
{
lean_object* v___x_1595_; 
lean_dec(v_numParams_1583_);
v___x_1595_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1580_, v_k_1581_, v_name_1582_, v_args_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
return v___x_1595_;
}
}
else
{
lean_object* v___x_1596_; 
lean_dec(v_numParams_1583_);
v___x_1596_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_1580_, v_k_1581_, v_name_1582_, v_args_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
return v___x_1596_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1598_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3));
v___x_1599_ = lean_unsigned_to_nat(14u);
v___x_1600_ = lean_unsigned_to_nat(185u);
v___x_1601_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1602_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1603_ = l_mkPanicMessageWithDecl(v___x_1602_, v___x_1601_, v___x_1600_, v___x_1599_, v___x_1598_);
return v___x_1603_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
v___x_1611_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(lean_object* v_decl_1620_, lean_object* v_k_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___x_1636_; lean_object* v_fvarId_1637_; lean_object* v_binderName_1638_; lean_object* v_type_1639_; lean_object* v_value_1640_; lean_object* v_subst_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_2353_; 
v___x_1636_ = lean_st_ref_get(v_a_1622_);
v_fvarId_1637_ = lean_ctor_get(v_decl_1620_, 0);
v_binderName_1638_ = lean_ctor_get(v_decl_1620_, 1);
v_type_1639_ = lean_ctor_get(v_decl_1620_, 2);
v_value_1640_ = lean_ctor_get(v_decl_1620_, 3);
v_subst_1641_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_2353_ == 0)
{
lean_object* v_unused_2354_; 
v_unused_2354_ = lean_ctor_get(v___x_1636_, 1);
lean_dec(v_unused_2354_);
v___x_1643_ = v___x_1636_;
v_isShared_1644_ = v_isSharedCheck_2353_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_subst_1641_);
lean_dec(v___x_1636_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_2353_;
goto v_resetjp_1642_;
}
v___jp_1628_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2);
v___x_1635_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1634_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1635_;
}
v_resetjp_1642_:
{
uint8_t v___x_1645_; uint8_t v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = 0;
v___x_1646_ = 1;
lean_inc(v_value_1640_);
v___x_1647_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v___x_1645_, v_subst_1641_, v_value_1640_, v___x_1646_);
lean_dec_ref(v_subst_1641_);
switch(lean_obj_tag(v___x_1647_))
{
case 0:
{
lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1664_; 
lean_inc(v_binderName_1638_);
lean_inc(v_fvarId_1637_);
lean_del_object(v___x_1643_);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_decl_1620_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; lean_object* v_unused_1666_; lean_object* v_unused_1667_; lean_object* v_unused_1668_; 
v_unused_1665_ = lean_ctor_get(v_decl_1620_, 3);
lean_dec(v_unused_1665_);
v_unused_1666_ = lean_ctor_get(v_decl_1620_, 2);
lean_dec(v_unused_1666_);
v_unused_1667_ = lean_ctor_get(v_decl_1620_, 1);
lean_dec(v_unused_1667_);
v_unused_1668_ = lean_ctor_get(v_decl_1620_, 0);
lean_dec(v_unused_1668_);
v___x_1649_ = v_decl_1620_;
v_isShared_1650_ = v_isSharedCheck_1664_;
goto v_resetjp_1648_;
}
else
{
lean_dec(v_decl_1620_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1664_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v_value_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1663_; 
v_value_1651_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1653_ = v___x_1647_;
v_isShared_1654_ = v_isSharedCheck_1663_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_value_1651_);
lean_dec(v___x_1647_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1663_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_value_1651_);
if (v_isShared_1654_ == 0)
{
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_value_1651_);
v___x_1657_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1659_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 3, v___x_1657_);
lean_ctor_set(v___x_1649_, 2, v___x_1655_);
v___x_1659_ = v___x_1649_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_fvarId_1637_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_binderName_1638_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1660_; 
v___x_1660_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1621_, v___x_1659_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1660_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1669_; 
lean_inc(v_fvarId_1637_);
lean_del_object(v___x_1643_);
lean_dec_ref(v_decl_1620_);
v___x_1669_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1621_, v_fvarId_1637_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1669_;
}
case 2:
{
lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1967_; 
lean_inc(v_binderName_1638_);
lean_inc(v_fvarId_1637_);
lean_del_object(v___x_1643_);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_decl_1620_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; lean_object* v_unused_1969_; lean_object* v_unused_1970_; lean_object* v_unused_1971_; 
v_unused_1968_ = lean_ctor_get(v_decl_1620_, 3);
lean_dec(v_unused_1968_);
v_unused_1969_ = lean_ctor_get(v_decl_1620_, 2);
lean_dec(v_unused_1969_);
v_unused_1970_ = lean_ctor_get(v_decl_1620_, 1);
lean_dec(v_unused_1970_);
v_unused_1971_ = lean_ctor_get(v_decl_1620_, 0);
lean_dec(v_unused_1971_);
v___x_1671_ = v_decl_1620_;
v_isShared_1672_ = v_isSharedCheck_1967_;
goto v_resetjp_1670_;
}
else
{
lean_dec(v_decl_1620_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1967_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v_typeName_1673_; lean_object* v_idx_1674_; lean_object* v_struct_1675_; lean_object* v___x_1676_; 
v_typeName_1673_ = lean_ctor_get(v___x_1647_, 0);
lean_inc_n(v_typeName_1673_, 2);
v_idx_1674_ = lean_ctor_get(v___x_1647_, 1);
lean_inc(v_idx_1674_);
v_struct_1675_ = lean_ctor_get(v___x_1647_, 2);
lean_inc(v_struct_1675_);
lean_dec_ref_known(v___x_1647_, 3);
v___x_1676_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_1673_, v_a_1625_, v_a_1626_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
if (lean_obj_tag(v_a_1677_) == 1)
{
lean_object* v_val_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1844_; 
lean_dec(v_typeName_1673_);
lean_del_object(v___x_1671_);
lean_dec(v_binderName_1638_);
v_val_1678_ = lean_ctor_get(v_a_1677_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_a_1677_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1680_ = v_a_1677_;
v_isShared_1681_ = v_isSharedCheck_1844_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_val_1678_);
lean_dec(v_a_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1844_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v_fieldIdx_1682_; uint8_t v___x_1683_; 
v_fieldIdx_1682_ = lean_ctor_get(v_val_1678_, 2);
lean_inc(v_fieldIdx_1682_);
lean_dec(v_val_1678_);
v___x_1683_ = lean_nat_dec_eq(v_fieldIdx_1682_, v_idx_1674_);
lean_dec(v_idx_1674_);
lean_dec(v_fieldIdx_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v_subst_1685_; lean_object* v_jpParamMask_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1762_; 
lean_del_object(v___x_1680_);
lean_dec(v_struct_1675_);
v___x_1684_ = lean_st_ref_take(v_a_1622_);
v_subst_1685_ = lean_ctor_get(v___x_1684_, 0);
v_jpParamMask_1686_ = lean_ctor_get(v___x_1684_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1688_ = v___x_1684_;
v_isShared_1689_ = v_isSharedCheck_1762_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_jpParamMask_1686_);
lean_inc(v_subst_1685_);
lean_dec(v___x_1684_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1762_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___y_1691_; lean_object* v___x_1697_; lean_object* v___y_1699_; lean_object* v_i_1700_; lean_object* v___y_1706_; lean_object* v___y_1716_; lean_object* v_i_1717_; lean_object* v___x_1732_; 
v___x_1697_ = lean_box(0);
v___x_1732_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1685_, v_fvarId_1637_);
switch(lean_obj_tag(v___x_1732_))
{
case 0:
{
lean_object* v_index_1733_; lean_object* v_size_1734_; lean_object* v___x_1735_; 
v_index_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_index_1733_);
lean_dec_ref_known(v___x_1732_, 3);
v_size_1734_ = lean_ctor_get(v_subst_1685_, 0);
lean_inc(v_size_1734_);
v___x_1735_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_1685_, v_size_1734_, v_index_1733_, v_fvarId_1637_, v___x_1697_);
lean_dec(v_index_1733_);
v___y_1691_ = v___x_1735_;
goto v___jp_1690_;
}
case 1:
{
lean_object* v_index_1736_; lean_object* v_size_1737_; lean_object* v_keyArray_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v_index_1736_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_index_1736_);
lean_dec_ref_known(v___x_1732_, 1);
v_size_1737_ = lean_ctor_get(v_subst_1685_, 0);
v_keyArray_1738_ = lean_ctor_get(v_subst_1685_, 1);
v___x_1739_ = lean_unsigned_to_nat(1u);
v___x_1740_ = lean_nat_add(v_size_1737_, v___x_1739_);
v___x_1741_ = lean_array_get_size(v_keyArray_1738_);
v___x_1742_ = lean_nat_dec_lt(v___x_1740_, v___x_1741_);
if (v___x_1742_ == 0)
{
lean_dec(v___x_1740_);
lean_dec(v_index_1736_);
goto v___jp_1722_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1743_ = lean_unsigned_to_nat(4u);
v___x_1744_ = lean_nat_mul(v___x_1740_, v___x_1743_);
v___x_1745_ = lean_unsigned_to_nat(3u);
v___x_1746_ = lean_nat_mul(v___x_1741_, v___x_1745_);
v___x_1747_ = lean_nat_dec_le(v___x_1744_, v___x_1746_);
lean_dec(v___x_1746_);
lean_dec(v___x_1744_);
if (v___x_1747_ == 0)
{
lean_dec(v___x_1740_);
lean_dec(v_index_1736_);
goto v___jp_1722_;
}
else
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_1685_, v___x_1740_, v_index_1736_, v_fvarId_1637_, v___x_1697_);
lean_dec(v_index_1736_);
v___y_1691_ = v___x_1748_;
goto v___jp_1690_;
}
}
}
default: 
{
lean_object* v_size_1749_; lean_object* v_keyArray_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_size_1749_ = lean_ctor_get(v_subst_1685_, 0);
v_keyArray_1750_ = lean_ctor_get(v_subst_1685_, 1);
v___x_1751_ = lean_unsigned_to_nat(1u);
v___x_1752_ = lean_nat_add(v_size_1749_, v___x_1751_);
v___x_1753_ = lean_array_get_size(v_keyArray_1750_);
v___x_1754_ = lean_nat_dec_lt(v___x_1752_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; 
lean_dec(v___x_1752_);
v___x_1755_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1685_);
lean_dec_ref(v_subst_1685_);
v___y_1706_ = v___x_1755_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1756_ = lean_unsigned_to_nat(4u);
v___x_1757_ = lean_nat_mul(v___x_1752_, v___x_1756_);
lean_dec(v___x_1752_);
v___x_1758_ = lean_unsigned_to_nat(3u);
v___x_1759_ = lean_nat_mul(v___x_1753_, v___x_1758_);
v___x_1760_ = lean_nat_dec_le(v___x_1757_, v___x_1759_);
lean_dec(v___x_1759_);
lean_dec(v___x_1757_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1685_);
lean_dec_ref(v_subst_1685_);
v___y_1706_ = v___x_1761_;
goto v___jp_1705_;
}
else
{
v___y_1706_ = v_subst_1685_;
goto v___jp_1705_;
}
}
}
}
v___jp_1690_:
{
lean_object* v___x_1693_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___y_1691_);
v___x_1693_ = v___x_1688_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___y_1691_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_jpParamMask_1686_);
v___x_1693_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_st_ref_put(v_a_1622_, v___x_1693_);
v___x_1695_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1695_;
}
}
v___jp_1698_:
{
lean_object* v_size_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v_size_1701_ = lean_ctor_get(v___y_1699_, 0);
v___x_1702_ = lean_unsigned_to_nat(1u);
v___x_1703_ = lean_nat_add(v_size_1701_, v___x_1702_);
v___x_1704_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1699_, v___x_1703_, v_i_1700_, v_fvarId_1637_, v___x_1697_);
lean_dec(v_i_1700_);
v___y_1691_ = v___x_1704_;
goto v___jp_1690_;
}
v___jp_1705_:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___y_1706_, v_fvarId_1637_);
switch(lean_obj_tag(v___x_1707_))
{
case 0:
{
lean_object* v_index_1708_; lean_object* v_size_1709_; lean_object* v___x_1710_; 
v_index_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_index_1708_);
lean_dec_ref_known(v___x_1707_, 3);
v_size_1709_ = lean_ctor_get(v___y_1706_, 0);
lean_inc(v_size_1709_);
v___x_1710_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1706_, v_size_1709_, v_index_1708_, v_fvarId_1637_, v___x_1697_);
lean_dec(v_index_1708_);
v___y_1691_ = v___x_1710_;
goto v___jp_1690_;
}
case 1:
{
lean_object* v_index_1711_; 
v_index_1711_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_index_1711_);
lean_dec_ref_known(v___x_1707_, 1);
v___y_1699_ = v___y_1706_;
v_i_1700_ = v_index_1711_;
goto v___jp_1698_;
}
default: 
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_unsigned_to_nat(0u);
v___x_1713_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1706_, v___x_1712_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_index_1714_; 
v_index_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_index_1714_);
lean_dec_ref_known(v___x_1713_, 1);
v___y_1699_ = v___y_1706_;
v_i_1700_ = v_index_1714_;
goto v___jp_1698_;
}
else
{
lean_dec(v_fvarId_1637_);
v___y_1691_ = v___y_1706_;
goto v___jp_1690_;
}
}
}
}
v___jp_1715_:
{
lean_object* v_size_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_size_1718_ = lean_ctor_get(v___y_1716_, 0);
v___x_1719_ = lean_unsigned_to_nat(1u);
v___x_1720_ = lean_nat_add(v_size_1718_, v___x_1719_);
v___x_1721_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1716_, v___x_1720_, v_i_1717_, v_fvarId_1637_, v___x_1697_);
lean_dec(v_i_1717_);
v___y_1691_ = v___x_1721_;
goto v___jp_1690_;
}
v___jp_1722_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1685_);
lean_dec_ref(v_subst_1685_);
v___x_1724_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___x_1723_, v_fvarId_1637_);
switch(lean_obj_tag(v___x_1724_))
{
case 0:
{
lean_object* v_index_1725_; lean_object* v_size_1726_; lean_object* v___x_1727_; 
v_index_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_index_1725_);
lean_dec_ref_known(v___x_1724_, 3);
v_size_1726_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_size_1726_);
v___x_1727_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1723_, v_size_1726_, v_index_1725_, v_fvarId_1637_, v___x_1697_);
lean_dec(v_index_1725_);
v___y_1691_ = v___x_1727_;
goto v___jp_1690_;
}
case 1:
{
lean_object* v_index_1728_; 
v_index_1728_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_index_1728_);
lean_dec_ref_known(v___x_1724_, 1);
v___y_1716_ = v___x_1723_;
v_i_1717_ = v_index_1728_;
goto v___jp_1715_;
}
default: 
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = lean_unsigned_to_nat(0u);
v___x_1730_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1723_, v___x_1729_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_index_1731_; 
v_index_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_index_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v___y_1716_ = v___x_1723_;
v_i_1717_ = v_index_1731_;
goto v___jp_1715_;
}
else
{
lean_dec(v_fvarId_1637_);
v___y_1691_ = v___x_1723_;
goto v___jp_1690_;
}
}
}
}
}
}
else
{
lean_object* v___x_1763_; lean_object* v_subst_1764_; lean_object* v_jpParamMask_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1843_; 
v___x_1763_ = lean_st_ref_take(v_a_1622_);
v_subst_1764_ = lean_ctor_get(v___x_1763_, 0);
v_jpParamMask_1765_ = lean_ctor_get(v___x_1763_, 1);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1767_ = v___x_1763_;
v_isShared_1768_ = v_isSharedCheck_1843_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_jpParamMask_1765_);
lean_inc(v_subst_1764_);
lean_dec(v___x_1763_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1843_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___y_1770_; lean_object* v___x_1777_; 
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v_struct_1675_);
v___x_1777_ = v___x_1680_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_struct_1675_);
v___x_1777_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1776_;
}
v___jp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___y_1770_);
v___x_1772_ = v___x_1767_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___y_1770_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_jpParamMask_1765_);
v___x_1772_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_st_ref_put(v_a_1622_, v___x_1772_);
v___x_1774_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1774_;
}
}
v_reusejp_1776_:
{
lean_object* v___y_1779_; lean_object* v_i_1780_; lean_object* v___y_1786_; lean_object* v___y_1796_; lean_object* v_i_1797_; lean_object* v___x_1812_; 
v___x_1812_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1764_, v_fvarId_1637_);
switch(lean_obj_tag(v___x_1812_))
{
case 0:
{
lean_object* v_index_1813_; lean_object* v_size_1814_; lean_object* v___x_1815_; 
v_index_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_index_1813_);
lean_dec_ref_known(v___x_1812_, 3);
v_size_1814_ = lean_ctor_get(v_subst_1764_, 0);
lean_inc(v_size_1814_);
v___x_1815_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_1764_, v_size_1814_, v_index_1813_, v_fvarId_1637_, v___x_1777_);
lean_dec(v_index_1813_);
v___y_1770_ = v___x_1815_;
goto v___jp_1769_;
}
case 1:
{
lean_object* v_index_1816_; lean_object* v_size_1817_; lean_object* v_keyArray_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v_index_1816_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_index_1816_);
lean_dec_ref_known(v___x_1812_, 1);
v_size_1817_ = lean_ctor_get(v_subst_1764_, 0);
v_keyArray_1818_ = lean_ctor_get(v_subst_1764_, 1);
v___x_1819_ = lean_unsigned_to_nat(1u);
v___x_1820_ = lean_nat_add(v_size_1817_, v___x_1819_);
v___x_1821_ = lean_array_get_size(v_keyArray_1818_);
v___x_1822_ = lean_nat_dec_lt(v___x_1820_, v___x_1821_);
if (v___x_1822_ == 0)
{
lean_dec(v___x_1820_);
lean_dec(v_index_1816_);
goto v___jp_1802_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1823_ = lean_unsigned_to_nat(4u);
v___x_1824_ = lean_nat_mul(v___x_1820_, v___x_1823_);
v___x_1825_ = lean_unsigned_to_nat(3u);
v___x_1826_ = lean_nat_mul(v___x_1821_, v___x_1825_);
v___x_1827_ = lean_nat_dec_le(v___x_1824_, v___x_1826_);
lean_dec(v___x_1826_);
lean_dec(v___x_1824_);
if (v___x_1827_ == 0)
{
lean_dec(v___x_1820_);
lean_dec(v_index_1816_);
goto v___jp_1802_;
}
else
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_1764_, v___x_1820_, v_index_1816_, v_fvarId_1637_, v___x_1777_);
lean_dec(v_index_1816_);
v___y_1770_ = v___x_1828_;
goto v___jp_1769_;
}
}
}
default: 
{
lean_object* v_size_1829_; lean_object* v_keyArray_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_size_1829_ = lean_ctor_get(v_subst_1764_, 0);
v_keyArray_1830_ = lean_ctor_get(v_subst_1764_, 1);
v___x_1831_ = lean_unsigned_to_nat(1u);
v___x_1832_ = lean_nat_add(v_size_1829_, v___x_1831_);
v___x_1833_ = lean_array_get_size(v_keyArray_1830_);
v___x_1834_ = lean_nat_dec_lt(v___x_1832_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
lean_dec(v___x_1832_);
v___x_1835_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1764_);
lean_dec_ref(v_subst_1764_);
v___y_1786_ = v___x_1835_;
goto v___jp_1785_;
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1836_ = lean_unsigned_to_nat(4u);
v___x_1837_ = lean_nat_mul(v___x_1832_, v___x_1836_);
lean_dec(v___x_1832_);
v___x_1838_ = lean_unsigned_to_nat(3u);
v___x_1839_ = lean_nat_mul(v___x_1833_, v___x_1838_);
v___x_1840_ = lean_nat_dec_le(v___x_1837_, v___x_1839_);
lean_dec(v___x_1839_);
lean_dec(v___x_1837_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1764_);
lean_dec_ref(v_subst_1764_);
v___y_1786_ = v___x_1841_;
goto v___jp_1785_;
}
else
{
v___y_1786_ = v_subst_1764_;
goto v___jp_1785_;
}
}
}
}
v___jp_1778_:
{
lean_object* v_size_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_size_1781_ = lean_ctor_get(v___y_1779_, 0);
v___x_1782_ = lean_unsigned_to_nat(1u);
v___x_1783_ = lean_nat_add(v_size_1781_, v___x_1782_);
v___x_1784_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1779_, v___x_1783_, v_i_1780_, v_fvarId_1637_, v___x_1777_);
lean_dec(v_i_1780_);
v___y_1770_ = v___x_1784_;
goto v___jp_1769_;
}
v___jp_1785_:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___y_1786_, v_fvarId_1637_);
switch(lean_obj_tag(v___x_1787_))
{
case 0:
{
lean_object* v_index_1788_; lean_object* v_size_1789_; lean_object* v___x_1790_; 
v_index_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_index_1788_);
lean_dec_ref_known(v___x_1787_, 3);
v_size_1789_ = lean_ctor_get(v___y_1786_, 0);
lean_inc(v_size_1789_);
v___x_1790_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1786_, v_size_1789_, v_index_1788_, v_fvarId_1637_, v___x_1777_);
lean_dec(v_index_1788_);
v___y_1770_ = v___x_1790_;
goto v___jp_1769_;
}
case 1:
{
lean_object* v_index_1791_; 
v_index_1791_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_index_1791_);
lean_dec_ref_known(v___x_1787_, 1);
v___y_1779_ = v___y_1786_;
v_i_1780_ = v_index_1791_;
goto v___jp_1778_;
}
default: 
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1786_, v___x_1792_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_index_1794_; 
v_index_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_index_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v___y_1779_ = v___y_1786_;
v_i_1780_ = v_index_1794_;
goto v___jp_1778_;
}
else
{
lean_dec_ref(v___x_1777_);
lean_dec(v_fvarId_1637_);
v___y_1770_ = v___y_1786_;
goto v___jp_1769_;
}
}
}
}
v___jp_1795_:
{
lean_object* v_size_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_size_1798_ = lean_ctor_get(v___y_1796_, 0);
v___x_1799_ = lean_unsigned_to_nat(1u);
v___x_1800_ = lean_nat_add(v_size_1798_, v___x_1799_);
v___x_1801_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1796_, v___x_1800_, v_i_1797_, v_fvarId_1637_, v___x_1777_);
lean_dec(v_i_1797_);
v___y_1770_ = v___x_1801_;
goto v___jp_1769_;
}
v___jp_1802_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1764_);
lean_dec_ref(v_subst_1764_);
v___x_1804_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___x_1803_, v_fvarId_1637_);
switch(lean_obj_tag(v___x_1804_))
{
case 0:
{
lean_object* v_index_1805_; lean_object* v_size_1806_; lean_object* v___x_1807_; 
v_index_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_index_1805_);
lean_dec_ref_known(v___x_1804_, 3);
v_size_1806_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_size_1806_);
v___x_1807_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1803_, v_size_1806_, v_index_1805_, v_fvarId_1637_, v___x_1777_);
lean_dec(v_index_1805_);
v___y_1770_ = v___x_1807_;
goto v___jp_1769_;
}
case 1:
{
lean_object* v_index_1808_; 
v_index_1808_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_index_1808_);
lean_dec_ref_known(v___x_1804_, 1);
v___y_1796_ = v___x_1803_;
v_i_1797_ = v_index_1808_;
goto v___jp_1795_;
}
default: 
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = lean_unsigned_to_nat(0u);
v___x_1810_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1803_, v___x_1809_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_index_1811_; 
v_index_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_index_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v___y_1796_ = v___x_1803_;
v_i_1797_ = v_index_1811_;
goto v___jp_1795_;
}
else
{
lean_dec_ref(v___x_1777_);
lean_dec(v_fvarId_1637_);
v___y_1770_ = v___x_1803_;
goto v___jp_1769_;
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
lean_object* v___x_1845_; lean_object* v_subst_1846_; lean_object* v___x_1847_; 
lean_dec(v_a_1677_);
v___x_1845_ = lean_st_ref_get(v_a_1622_);
v_subst_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc_ref(v_subst_1846_);
lean_dec(v___x_1845_);
v___x_1847_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1846_, v_struct_1675_, v___x_1646_);
lean_dec_ref(v_subst_1846_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_fvarId_1848_; lean_object* v___x_1849_; lean_object* v_env_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; 
v_fvarId_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_fvarId_1848_);
lean_dec_ref_known(v___x_1847_, 1);
v___x_1849_ = lean_st_ref_get(v_a_1626_);
v_env_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc_ref(v_env_1850_);
lean_dec(v___x_1849_);
v___x_1851_ = 0;
v___x_1852_ = l_Lean_Environment_find_x3f(v_env_1850_, v_typeName_1673_, v___x_1851_);
if (lean_obj_tag(v___x_1852_) == 1)
{
lean_object* v_val_1853_; 
v_val_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_val_1853_);
lean_dec_ref_known(v___x_1852_, 1);
if (lean_obj_tag(v_val_1853_) == 5)
{
lean_object* v_val_1854_; lean_object* v_ctors_1855_; 
v_val_1854_ = lean_ctor_get(v_val_1853_, 0);
lean_inc_ref(v_val_1854_);
lean_dec_ref_known(v_val_1853_, 1);
v_ctors_1855_ = lean_ctor_get(v_val_1854_, 4);
lean_inc(v_ctors_1855_);
lean_dec_ref(v_val_1854_);
if (lean_obj_tag(v_ctors_1855_) == 1)
{
lean_object* v_tail_1856_; 
v_tail_1856_ = lean_ctor_get(v_ctors_1855_, 1);
if (lean_obj_tag(v_tail_1856_) == 0)
{
lean_object* v_head_1857_; lean_object* v___x_1858_; 
v_head_1857_ = lean_ctor_get(v_ctors_1855_, 0);
lean_inc(v_head_1857_);
lean_dec_ref_known(v_ctors_1855_, 2);
v___x_1858_ = l_Lean_Compiler_LCNF_getCtorLayout(v_head_1857_, v_a_1625_, v_a_1626_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v_ctorInfo_1860_; lean_object* v_fieldInfo_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v_fst_1865_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___x_1858_, 1);
v_ctorInfo_1860_ = lean_ctor_get(v_a_1859_, 0);
lean_inc_ref(v_ctorInfo_1860_);
v_fieldInfo_1861_ = lean_ctor_get(v_a_1859_, 1);
lean_inc_ref(v_fieldInfo_1861_);
lean_dec(v_a_1859_);
v___x_1862_ = lean_box(0);
v___x_1863_ = lean_array_get(v___x_1862_, v_fieldInfo_1861_, v_idx_1674_);
lean_dec(v_idx_1674_);
lean_dec_ref(v_fieldInfo_1861_);
v___x_1864_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_fvarId_1848_, v_ctorInfo_1860_, v___x_1863_);
lean_dec_ref(v_ctorInfo_1860_);
v_fst_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_fst_1865_);
if (lean_obj_tag(v_fst_1865_) == 1)
{
lean_object* v___x_1866_; 
lean_dec_ref(v___x_1864_);
lean_del_object(v___x_1671_);
lean_dec(v_binderName_1638_);
v___x_1866_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1621_, v_fvarId_1637_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1866_;
}
else
{
lean_object* v_snd_1867_; lean_object* v___x_1869_; 
v_snd_1867_ = lean_ctor_get(v___x_1864_, 1);
lean_inc(v_snd_1867_);
lean_dec_ref(v___x_1864_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 3, v_fst_1865_);
lean_ctor_set(v___x_1671_, 2, v_snd_1867_);
v___x_1869_ = v___x_1671_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_fvarId_1637_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_binderName_1638_);
lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_snd_1867_);
lean_ctor_set(v_reuseFailAlloc_1871_, 3, v_fst_1865_);
v___x_1869_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; 
v___x_1870_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1621_, v___x_1869_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1870_;
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec(v_fvarId_1848_);
lean_dec(v_idx_1674_);
lean_del_object(v___x_1671_);
lean_dec(v_binderName_1638_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1621_);
v_a_1872_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1858_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1858_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1855_, 2);
lean_dec(v_fvarId_1848_);
lean_dec(v_idx_1674_);
lean_del_object(v___x_1671_);
lean_dec(v_binderName_1638_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1621_);
v___y_1629_ = v_a_1622_;
v___y_1630_ = v_a_1623_;
v___y_1631_ = v_a_1624_;
v___y_1632_ = v_a_1625_;
v___y_1633_ = v_a_1626_;
goto v___jp_1628_;
}
}
else
{
lean_dec(v_ctors_1855_);
lean_dec(v_fvarId_1848_);
lean_dec(v_idx_1674_);
lean_del_object(v___x_1671_);
lean_dec(v_binderName_1638_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1621_);
v___y_1629_ = v_a_1622_;
v___y_1630_ = v_a_1623_;
v___y_1631_ = v_a_1624_;
v___y_1632_ = v_a_1625_;
v___y_1633_ = v_a_1626_;
goto v___jp_1628_;
}
}
else
{
lean_dec(v_val_1853_);
lean_dec(v_fvarId_1848_);
lean_dec(v_idx_1674_);
lean_del_object(v___x_1671_);
lean_dec(v_binderName_1638_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1621_);
v___y_1629_ = v_a_1622_;
v___y_1630_ = v_a_1623_;
v___y_1631_ = v_a_1624_;
v___y_1632_ = v_a_1625_;
v___y_1633_ = v_a_1626_;
goto v___jp_1628_;
}
}
else
{
lean_dec(v___x_1852_);
lean_dec(v_fvarId_1848_);
lean_dec(v_idx_1674_);
lean_del_object(v___x_1671_);
lean_dec(v_binderName_1638_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1621_);
v___y_1629_ = v_a_1622_;
v___y_1630_ = v_a_1623_;
v___y_1631_ = v_a_1624_;
v___y_1632_ = v_a_1625_;
v___y_1633_ = v_a_1626_;
goto v___jp_1628_;
}
}
else
{
lean_object* v___x_1880_; lean_object* v_subst_1881_; lean_object* v_jpParamMask_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1958_; 
lean_dec(v_idx_1674_);
lean_dec(v_typeName_1673_);
lean_del_object(v___x_1671_);
lean_dec(v_binderName_1638_);
v___x_1880_ = lean_st_ref_take(v_a_1622_);
v_subst_1881_ = lean_ctor_get(v___x_1880_, 0);
v_jpParamMask_1882_ = lean_ctor_get(v___x_1880_, 1);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1884_ = v___x_1880_;
v_isShared_1885_ = v_isSharedCheck_1958_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_jpParamMask_1882_);
lean_inc(v_subst_1881_);
lean_dec(v___x_1880_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1958_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___y_1887_; lean_object* v___x_1893_; lean_object* v___y_1895_; lean_object* v_i_1896_; lean_object* v___y_1902_; lean_object* v___y_1912_; lean_object* v_i_1913_; lean_object* v___x_1928_; 
v___x_1893_ = lean_box(0);
v___x_1928_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1881_, v_fvarId_1637_);
switch(lean_obj_tag(v___x_1928_))
{
case 0:
{
lean_object* v_index_1929_; lean_object* v_size_1930_; lean_object* v___x_1931_; 
v_index_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_index_1929_);
lean_dec_ref_known(v___x_1928_, 3);
v_size_1930_ = lean_ctor_get(v_subst_1881_, 0);
lean_inc(v_size_1930_);
v___x_1931_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_1881_, v_size_1930_, v_index_1929_, v_fvarId_1637_, v___x_1893_);
lean_dec(v_index_1929_);
v___y_1887_ = v___x_1931_;
goto v___jp_1886_;
}
case 1:
{
lean_object* v_index_1932_; lean_object* v_size_1933_; lean_object* v_keyArray_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v_index_1932_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_index_1932_);
lean_dec_ref_known(v___x_1928_, 1);
v_size_1933_ = lean_ctor_get(v_subst_1881_, 0);
v_keyArray_1934_ = lean_ctor_get(v_subst_1881_, 1);
v___x_1935_ = lean_unsigned_to_nat(1u);
v___x_1936_ = lean_nat_add(v_size_1933_, v___x_1935_);
v___x_1937_ = lean_array_get_size(v_keyArray_1934_);
v___x_1938_ = lean_nat_dec_lt(v___x_1936_, v___x_1937_);
if (v___x_1938_ == 0)
{
lean_dec(v___x_1936_);
lean_dec(v_index_1932_);
goto v___jp_1918_;
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1939_ = lean_unsigned_to_nat(4u);
v___x_1940_ = lean_nat_mul(v___x_1936_, v___x_1939_);
v___x_1941_ = lean_unsigned_to_nat(3u);
v___x_1942_ = lean_nat_mul(v___x_1937_, v___x_1941_);
v___x_1943_ = lean_nat_dec_le(v___x_1940_, v___x_1942_);
lean_dec(v___x_1942_);
lean_dec(v___x_1940_);
if (v___x_1943_ == 0)
{
lean_dec(v___x_1936_);
lean_dec(v_index_1932_);
goto v___jp_1918_;
}
else
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_1881_, v___x_1936_, v_index_1932_, v_fvarId_1637_, v___x_1893_);
lean_dec(v_index_1932_);
v___y_1887_ = v___x_1944_;
goto v___jp_1886_;
}
}
}
default: 
{
lean_object* v_size_1945_; lean_object* v_keyArray_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v_size_1945_ = lean_ctor_get(v_subst_1881_, 0);
v_keyArray_1946_ = lean_ctor_get(v_subst_1881_, 1);
v___x_1947_ = lean_unsigned_to_nat(1u);
v___x_1948_ = lean_nat_add(v_size_1945_, v___x_1947_);
v___x_1949_ = lean_array_get_size(v_keyArray_1946_);
v___x_1950_ = lean_nat_dec_lt(v___x_1948_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; 
lean_dec(v___x_1948_);
v___x_1951_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1881_);
lean_dec_ref(v_subst_1881_);
v___y_1902_ = v___x_1951_;
goto v___jp_1901_;
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1952_ = lean_unsigned_to_nat(4u);
v___x_1953_ = lean_nat_mul(v___x_1948_, v___x_1952_);
lean_dec(v___x_1948_);
v___x_1954_ = lean_unsigned_to_nat(3u);
v___x_1955_ = lean_nat_mul(v___x_1949_, v___x_1954_);
v___x_1956_ = lean_nat_dec_le(v___x_1953_, v___x_1955_);
lean_dec(v___x_1955_);
lean_dec(v___x_1953_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1881_);
lean_dec_ref(v_subst_1881_);
v___y_1902_ = v___x_1957_;
goto v___jp_1901_;
}
else
{
v___y_1902_ = v_subst_1881_;
goto v___jp_1901_;
}
}
}
}
v___jp_1886_:
{
lean_object* v___x_1889_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___y_1887_);
v___x_1889_ = v___x_1884_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___y_1887_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_jpParamMask_1882_);
v___x_1889_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_st_ref_put(v_a_1622_, v___x_1889_);
v___x_1891_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1891_;
}
}
v___jp_1894_:
{
lean_object* v_size_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v_size_1897_ = lean_ctor_get(v___y_1895_, 0);
v___x_1898_ = lean_unsigned_to_nat(1u);
v___x_1899_ = lean_nat_add(v_size_1897_, v___x_1898_);
v___x_1900_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1895_, v___x_1899_, v_i_1896_, v_fvarId_1637_, v___x_1893_);
lean_dec(v_i_1896_);
v___y_1887_ = v___x_1900_;
goto v___jp_1886_;
}
v___jp_1901_:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___y_1902_, v_fvarId_1637_);
switch(lean_obj_tag(v___x_1903_))
{
case 0:
{
lean_object* v_index_1904_; lean_object* v_size_1905_; lean_object* v___x_1906_; 
v_index_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_index_1904_);
lean_dec_ref_known(v___x_1903_, 3);
v_size_1905_ = lean_ctor_get(v___y_1902_, 0);
lean_inc(v_size_1905_);
v___x_1906_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1902_, v_size_1905_, v_index_1904_, v_fvarId_1637_, v___x_1893_);
lean_dec(v_index_1904_);
v___y_1887_ = v___x_1906_;
goto v___jp_1886_;
}
case 1:
{
lean_object* v_index_1907_; 
v_index_1907_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_index_1907_);
lean_dec_ref_known(v___x_1903_, 1);
v___y_1895_ = v___y_1902_;
v_i_1896_ = v_index_1907_;
goto v___jp_1894_;
}
default: 
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1902_, v___x_1908_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_index_1910_; 
v_index_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_index_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v___y_1895_ = v___y_1902_;
v_i_1896_ = v_index_1910_;
goto v___jp_1894_;
}
else
{
lean_dec(v_fvarId_1637_);
v___y_1887_ = v___y_1902_;
goto v___jp_1886_;
}
}
}
}
v___jp_1911_:
{
lean_object* v_size_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_size_1914_ = lean_ctor_get(v___y_1912_, 0);
v___x_1915_ = lean_unsigned_to_nat(1u);
v___x_1916_ = lean_nat_add(v_size_1914_, v___x_1915_);
v___x_1917_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1912_, v___x_1916_, v_i_1913_, v_fvarId_1637_, v___x_1893_);
lean_dec(v_i_1913_);
v___y_1887_ = v___x_1917_;
goto v___jp_1886_;
}
v___jp_1918_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_1881_);
lean_dec_ref(v_subst_1881_);
v___x_1920_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___x_1919_, v_fvarId_1637_);
switch(lean_obj_tag(v___x_1920_))
{
case 0:
{
lean_object* v_index_1921_; lean_object* v_size_1922_; lean_object* v___x_1923_; 
v_index_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_index_1921_);
lean_dec_ref_known(v___x_1920_, 3);
v_size_1922_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_size_1922_);
v___x_1923_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1919_, v_size_1922_, v_index_1921_, v_fvarId_1637_, v___x_1893_);
lean_dec(v_index_1921_);
v___y_1887_ = v___x_1923_;
goto v___jp_1886_;
}
case 1:
{
lean_object* v_index_1924_; 
v_index_1924_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_index_1924_);
lean_dec_ref_known(v___x_1920_, 1);
v___y_1912_ = v___x_1919_;
v_i_1913_ = v_index_1924_;
goto v___jp_1911_;
}
default: 
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1919_, v___x_1925_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_index_1927_; 
v_index_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_index_1927_);
lean_dec_ref_known(v___x_1926_, 1);
v___y_1912_ = v___x_1919_;
v_i_1913_ = v_index_1927_;
goto v___jp_1911_;
}
else
{
lean_dec(v_fvarId_1637_);
v___y_1887_ = v___x_1919_;
goto v___jp_1886_;
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
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v_struct_1675_);
lean_dec(v_idx_1674_);
lean_dec(v_typeName_1673_);
lean_del_object(v___x_1671_);
lean_dec(v_binderName_1638_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1621_);
v_a_1959_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1676_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1676_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
case 3:
{
lean_object* v_declName_1972_; lean_object* v_args_1973_; size_t v_sz_1974_; size_t v___x_1975_; lean_object* v___x_1976_; 
v_declName_1972_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_declName_1972_);
v_args_1973_ = lean_ctor_get(v___x_1647_, 2);
lean_inc_ref_n(v_args_1973_, 2);
lean_dec_ref_known(v___x_1647_, 3);
v_sz_1974_ = lean_array_size(v_args_1973_);
v___x_1975_ = ((size_t)0ULL);
v___x_1976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_1974_, v___x_1975_, v_args_1973_, v_a_1622_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1978_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
lean_inc(v_declName_1972_);
v___x_1978_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1972_, v_a_1626_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
if (lean_obj_tag(v_a_1979_) == 1)
{
lean_object* v_val_1980_; lean_object* v_params_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
lean_dec_ref(v_args_1973_);
lean_del_object(v___x_1643_);
v_val_1980_ = lean_ctor_get(v_a_1979_, 0);
lean_inc(v_val_1980_);
lean_dec_ref_known(v_a_1979_, 1);
v_params_1981_ = lean_ctor_get(v_val_1980_, 3);
lean_inc_ref(v_params_1981_);
lean_dec(v_val_1980_);
v___x_1982_ = lean_array_get_size(v_params_1981_);
lean_dec_ref(v_params_1981_);
v___x_1983_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1620_, v_k_1621_, v_declName_1972_, v___x_1982_, v_a_1977_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1983_;
}
else
{
lean_object* v___x_1984_; 
lean_dec(v_a_1979_);
lean_inc(v_declName_1972_);
v___x_1984_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1972_, v_a_1626_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
if (lean_obj_tag(v_a_1985_) == 1)
{
lean_object* v_val_1986_; lean_object* v_toSignature_1987_; lean_object* v_params_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_dec_ref(v_args_1973_);
lean_del_object(v___x_1643_);
v_val_1986_ = lean_ctor_get(v_a_1985_, 0);
lean_inc(v_val_1986_);
lean_dec_ref_known(v_a_1985_, 1);
v_toSignature_1987_ = lean_ctor_get(v_val_1986_, 0);
lean_inc_ref(v_toSignature_1987_);
lean_dec(v_val_1986_);
v_params_1988_ = lean_ctor_get(v_toSignature_1987_, 3);
lean_inc_ref(v_params_1988_);
lean_dec_ref(v_toSignature_1987_);
v___x_1989_ = lean_array_get_size(v_params_1988_);
lean_dec_ref(v_params_1988_);
v___x_1990_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1620_, v_k_1621_, v_declName_1972_, v___x_1989_, v_a_1977_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1990_;
}
else
{
lean_object* v___x_1991_; lean_object* v_env_1992_; uint8_t v___x_1993_; lean_object* v___x_1994_; 
lean_dec(v_a_1985_);
v___x_1991_ = lean_st_ref_get(v_a_1626_);
v_env_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc_ref(v_env_1992_);
lean_dec(v___x_1991_);
v___x_1993_ = 0;
lean_inc(v_declName_1972_);
v___x_1994_ = l_Lean_Environment_find_x3f(v_env_1992_, v_declName_1972_, v___x_1993_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_dec(v_a_1977_);
lean_dec_ref(v_args_1973_);
lean_dec(v_declName_1972_);
lean_del_object(v___x_1643_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
v___x_1995_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4);
v___x_1996_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1995_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1996_;
}
else
{
lean_object* v_val_1997_; 
v_val_1997_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_val_1997_);
lean_dec_ref_known(v___x_1994_, 1);
switch(lean_obj_tag(v_val_1997_))
{
case 0:
{
lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v_a_1977_);
lean_dec_ref(v_args_1973_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_val_1997_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; 
v_unused_2014_ = lean_ctor_get(v_val_1997_, 0);
lean_dec(v_unused_2014_);
v___x_1999_ = v_val_1997_;
v_isShared_2000_ = v_isSharedCheck_2013_;
goto v_resetjp_1998_;
}
else
{
lean_dec(v_val_1997_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2013_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2001_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_2002_ = l_Lean_Name_toString(v_declName_1972_, v___x_1646_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set_tag(v___x_1999_, 3);
lean_ctor_set(v___x_1999_, 0, v___x_2002_);
v___x_2004_ = v___x_1999_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 5);
lean_ctor_set(v___x_1643_, 1, v___x_2004_);
lean_ctor_set(v___x_1643_, 0, v___x_2001_);
v___x_2006_ = v___x_1643_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2007_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_2008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2006_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = l_Lean_MessageData_ofFormat(v___x_2008_);
v___x_2010_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2009_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_2010_;
}
}
}
}
case 2:
{
lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2030_; 
lean_dec(v_a_1977_);
lean_dec_ref(v_args_1973_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_val_1997_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v_val_1997_, 0);
lean_dec(v_unused_2031_);
v___x_2016_ = v_val_1997_;
v_isShared_2017_ = v_isSharedCheck_2030_;
goto v_resetjp_2015_;
}
else
{
lean_dec(v_val_1997_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2030_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2018_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_2019_ = l_Lean_Name_toString(v_declName_1972_, v___x_1646_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set_tag(v___x_2016_, 3);
lean_ctor_set(v___x_2016_, 0, v___x_2019_);
v___x_2021_ = v___x_2016_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2023_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 5);
lean_ctor_set(v___x_1643_, 1, v___x_2021_);
lean_ctor_set(v___x_1643_, 0, v___x_2018_);
v___x_2023_ = v___x_1643_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2024_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_2025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2023_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = l_Lean_MessageData_ofFormat(v___x_2025_);
v___x_2027_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2026_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_2027_;
}
}
}
}
case 4:
{
lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_a_1977_);
lean_dec_ref(v_args_1973_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_val_1997_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v_val_1997_, 0);
lean_dec(v_unused_2048_);
v___x_2033_ = v_val_1997_;
v_isShared_2034_ = v_isSharedCheck_2047_;
goto v_resetjp_2032_;
}
else
{
lean_dec(v_val_1997_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2047_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2035_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_2036_ = l_Lean_Name_toString(v_declName_1972_, v___x_1646_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 3);
lean_ctor_set(v___x_2033_, 0, v___x_2036_);
v___x_2038_ = v___x_2033_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 5);
lean_ctor_set(v___x_1643_, 1, v___x_2038_);
lean_ctor_set(v___x_1643_, 0, v___x_2035_);
v___x_2040_ = v___x_1643_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2041_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_2042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2040_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = l_Lean_MessageData_ofFormat(v___x_2042_);
v___x_2044_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2043_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_2044_;
}
}
}
}
case 5:
{
lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_a_1977_);
lean_dec_ref(v_args_1973_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_val_1997_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v_val_1997_, 0);
lean_dec(v_unused_2065_);
v___x_2050_ = v_val_1997_;
v_isShared_2051_ = v_isSharedCheck_2064_;
goto v_resetjp_2049_;
}
else
{
lean_dec(v_val_1997_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2064_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2052_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_2053_ = l_Lean_Name_toString(v_declName_1972_, v___x_1646_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set_tag(v___x_2050_, 3);
lean_ctor_set(v___x_2050_, 0, v___x_2053_);
v___x_2055_ = v___x_2050_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2057_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 5);
lean_ctor_set(v___x_1643_, 1, v___x_2055_);
lean_ctor_set(v___x_1643_, 0, v___x_2052_);
v___x_2057_ = v___x_1643_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2058_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_2059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = l_Lean_MessageData_ofFormat(v___x_2059_);
v___x_2061_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2060_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_2061_;
}
}
}
}
case 6:
{
lean_object* v_val_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2266_; 
v_val_2066_ = lean_ctor_get(v_val_1997_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_val_1997_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2068_ = v_val_1997_;
v_isShared_2069_ = v_isSharedCheck_2266_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_val_2066_);
lean_dec(v_val_1997_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2266_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v_induct_2070_; lean_object* v_cidx_2071_; lean_object* v_numParams_2072_; lean_object* v___x_2073_; 
v_induct_2070_ = lean_ctor_get(v_val_2066_, 1);
lean_inc_n(v_induct_2070_, 2);
v_cidx_2071_ = lean_ctor_get(v_val_2066_, 2);
lean_inc(v_cidx_2071_);
v_numParams_2072_ = lean_ctor_get(v_val_2066_, 3);
lean_inc(v_numParams_2072_);
lean_dec_ref(v_val_2066_);
v___x_2073_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_induct_2070_, v_a_1625_, v_a_1626_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2073_, 1);
if (lean_obj_tag(v_a_2074_) == 1)
{
lean_object* v_val_2075_; lean_object* v___x_2076_; lean_object* v_numParams_2077_; lean_object* v_fieldIdx_2078_; lean_object* v_subst_2079_; lean_object* v_jpParamMask_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2158_; 
lean_inc(v_fvarId_1637_);
lean_dec(v_numParams_2072_);
lean_dec(v_cidx_2071_);
lean_dec(v_induct_2070_);
lean_del_object(v___x_2068_);
lean_dec(v_a_1977_);
lean_dec(v_declName_1972_);
lean_del_object(v___x_1643_);
lean_dec_ref(v_decl_1620_);
v_val_2075_ = lean_ctor_get(v_a_2074_, 0);
lean_inc(v_val_2075_);
lean_dec_ref_known(v_a_2074_, 1);
v___x_2076_ = lean_st_ref_take(v_a_1622_);
v_numParams_2077_ = lean_ctor_get(v_val_2075_, 1);
lean_inc(v_numParams_2077_);
v_fieldIdx_2078_ = lean_ctor_get(v_val_2075_, 2);
lean_inc(v_fieldIdx_2078_);
lean_dec(v_val_2075_);
v_subst_2079_ = lean_ctor_get(v___x_2076_, 0);
v_jpParamMask_2080_ = lean_ctor_get(v___x_2076_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2082_ = v___x_2076_;
v_isShared_2083_ = v_isSharedCheck_2158_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_jpParamMask_2080_);
lean_inc(v_subst_2079_);
lean_dec(v___x_2076_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2158_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___y_2085_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___y_2095_; lean_object* v_i_2096_; lean_object* v___y_2102_; lean_object* v___y_2112_; lean_object* v_i_2113_; lean_object* v___x_2128_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = lean_nat_add(v_numParams_2077_, v_fieldIdx_2078_);
lean_dec(v_fieldIdx_2078_);
lean_dec(v_numParams_2077_);
v___x_2093_ = lean_array_get(v___x_2091_, v_args_1973_, v___x_2092_);
lean_dec(v___x_2092_);
lean_dec_ref(v_args_1973_);
v___x_2128_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_2079_, v_fvarId_1637_);
switch(lean_obj_tag(v___x_2128_))
{
case 0:
{
lean_object* v_index_2129_; lean_object* v_size_2130_; lean_object* v___x_2131_; 
v_index_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_index_2129_);
lean_dec_ref_known(v___x_2128_, 3);
v_size_2130_ = lean_ctor_get(v_subst_2079_, 0);
lean_inc(v_size_2130_);
v___x_2131_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_2079_, v_size_2130_, v_index_2129_, v_fvarId_1637_, v___x_2093_);
lean_dec(v_index_2129_);
v___y_2085_ = v___x_2131_;
goto v___jp_2084_;
}
case 1:
{
lean_object* v_index_2132_; lean_object* v_size_2133_; lean_object* v_keyArray_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v_index_2132_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_index_2132_);
lean_dec_ref_known(v___x_2128_, 1);
v_size_2133_ = lean_ctor_get(v_subst_2079_, 0);
v_keyArray_2134_ = lean_ctor_get(v_subst_2079_, 1);
v___x_2135_ = lean_unsigned_to_nat(1u);
v___x_2136_ = lean_nat_add(v_size_2133_, v___x_2135_);
v___x_2137_ = lean_array_get_size(v_keyArray_2134_);
v___x_2138_ = lean_nat_dec_lt(v___x_2136_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_dec(v___x_2136_);
lean_dec(v_index_2132_);
goto v___jp_2118_;
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2139_ = lean_unsigned_to_nat(4u);
v___x_2140_ = lean_nat_mul(v___x_2136_, v___x_2139_);
v___x_2141_ = lean_unsigned_to_nat(3u);
v___x_2142_ = lean_nat_mul(v___x_2137_, v___x_2141_);
v___x_2143_ = lean_nat_dec_le(v___x_2140_, v___x_2142_);
lean_dec(v___x_2142_);
lean_dec(v___x_2140_);
if (v___x_2143_ == 0)
{
lean_dec(v___x_2136_);
lean_dec(v_index_2132_);
goto v___jp_2118_;
}
else
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_2079_, v___x_2136_, v_index_2132_, v_fvarId_1637_, v___x_2093_);
lean_dec(v_index_2132_);
v___y_2085_ = v___x_2144_;
goto v___jp_2084_;
}
}
}
default: 
{
lean_object* v_size_2145_; lean_object* v_keyArray_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v_size_2145_ = lean_ctor_get(v_subst_2079_, 0);
v_keyArray_2146_ = lean_ctor_get(v_subst_2079_, 1);
v___x_2147_ = lean_unsigned_to_nat(1u);
v___x_2148_ = lean_nat_add(v_size_2145_, v___x_2147_);
v___x_2149_ = lean_array_get_size(v_keyArray_2146_);
v___x_2150_ = lean_nat_dec_lt(v___x_2148_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; 
lean_dec(v___x_2148_);
v___x_2151_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_2079_);
lean_dec_ref(v_subst_2079_);
v___y_2102_ = v___x_2151_;
goto v___jp_2101_;
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2152_ = lean_unsigned_to_nat(4u);
v___x_2153_ = lean_nat_mul(v___x_2148_, v___x_2152_);
lean_dec(v___x_2148_);
v___x_2154_ = lean_unsigned_to_nat(3u);
v___x_2155_ = lean_nat_mul(v___x_2149_, v___x_2154_);
v___x_2156_ = lean_nat_dec_le(v___x_2153_, v___x_2155_);
lean_dec(v___x_2155_);
lean_dec(v___x_2153_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_2079_);
lean_dec_ref(v_subst_2079_);
v___y_2102_ = v___x_2157_;
goto v___jp_2101_;
}
else
{
v___y_2102_ = v_subst_2079_;
goto v___jp_2101_;
}
}
}
}
v___jp_2084_:
{
lean_object* v___x_2087_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___y_2085_);
v___x_2087_ = v___x_2082_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___y_2085_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_jpParamMask_2080_);
v___x_2087_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_st_ref_put(v_a_1622_, v___x_2087_);
v___x_2089_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_2089_;
}
}
v___jp_2094_:
{
lean_object* v_size_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_size_2097_ = lean_ctor_get(v___y_2095_, 0);
v___x_2098_ = lean_unsigned_to_nat(1u);
v___x_2099_ = lean_nat_add(v_size_2097_, v___x_2098_);
v___x_2100_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2095_, v___x_2099_, v_i_2096_, v_fvarId_1637_, v___x_2093_);
lean_dec(v_i_2096_);
v___y_2085_ = v___x_2100_;
goto v___jp_2084_;
}
v___jp_2101_:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___y_2102_, v_fvarId_1637_);
switch(lean_obj_tag(v___x_2103_))
{
case 0:
{
lean_object* v_index_2104_; lean_object* v_size_2105_; lean_object* v___x_2106_; 
v_index_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_index_2104_);
lean_dec_ref_known(v___x_2103_, 3);
v_size_2105_ = lean_ctor_get(v___y_2102_, 0);
lean_inc(v_size_2105_);
v___x_2106_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2102_, v_size_2105_, v_index_2104_, v_fvarId_1637_, v___x_2093_);
lean_dec(v_index_2104_);
v___y_2085_ = v___x_2106_;
goto v___jp_2084_;
}
case 1:
{
lean_object* v_index_2107_; 
v_index_2107_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_index_2107_);
lean_dec_ref_known(v___x_2103_, 1);
v___y_2095_ = v___y_2102_;
v_i_2096_ = v_index_2107_;
goto v___jp_2094_;
}
default: 
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = lean_unsigned_to_nat(0u);
v___x_2109_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2102_, v___x_2108_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_index_2110_; 
v_index_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_index_2110_);
lean_dec_ref_known(v___x_2109_, 1);
v___y_2095_ = v___y_2102_;
v_i_2096_ = v_index_2110_;
goto v___jp_2094_;
}
else
{
lean_dec(v___x_2093_);
lean_dec(v_fvarId_1637_);
v___y_2085_ = v___y_2102_;
goto v___jp_2084_;
}
}
}
}
v___jp_2111_:
{
lean_object* v_size_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_size_2114_ = lean_ctor_get(v___y_2112_, 0);
v___x_2115_ = lean_unsigned_to_nat(1u);
v___x_2116_ = lean_nat_add(v_size_2114_, v___x_2115_);
v___x_2117_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2112_, v___x_2116_, v_i_2113_, v_fvarId_1637_, v___x_2093_);
lean_dec(v_i_2113_);
v___y_2085_ = v___x_2117_;
goto v___jp_2084_;
}
v___jp_2118_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_2079_);
lean_dec_ref(v_subst_2079_);
v___x_2120_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___x_2119_, v_fvarId_1637_);
switch(lean_obj_tag(v___x_2120_))
{
case 0:
{
lean_object* v_index_2121_; lean_object* v_size_2122_; lean_object* v___x_2123_; 
v_index_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_index_2121_);
lean_dec_ref_known(v___x_2120_, 3);
v_size_2122_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_size_2122_);
v___x_2123_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2119_, v_size_2122_, v_index_2121_, v_fvarId_1637_, v___x_2093_);
lean_dec(v_index_2121_);
v___y_2085_ = v___x_2123_;
goto v___jp_2084_;
}
case 1:
{
lean_object* v_index_2124_; 
v_index_2124_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_index_2124_);
lean_dec_ref_known(v___x_2120_, 1);
v___y_2112_ = v___x_2119_;
v_i_2113_ = v_index_2124_;
goto v___jp_2111_;
}
default: 
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2119_, v___x_2125_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_index_2127_; 
v_index_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_index_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___y_2112_ = v___x_2119_;
v_i_2113_ = v_index_2127_;
goto v___jp_2111_;
}
else
{
lean_dec(v___x_2093_);
lean_dec(v_fvarId_1637_);
v___y_2085_ = v___x_2119_;
goto v___jp_2084_;
}
}
}
}
}
}
else
{
lean_object* v___x_2159_; 
lean_dec(v_a_2074_);
lean_dec_ref(v_args_1973_);
v___x_2159_ = l_Lean_Compiler_LCNF_nameToImpureType(v_induct_2070_, v_a_1625_, v_a_1626_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; uint8_t v___x_2161_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2161_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; 
lean_dec(v_a_2160_);
lean_dec(v_cidx_2071_);
lean_del_object(v___x_2068_);
v___x_2162_ = l_Lean_Compiler_LCNF_getCtorLayout(v_declName_1972_, v_a_1625_, v_a_1626_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2225_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2165_ = v___x_2162_;
v_isShared_2166_ = v_isSharedCheck_2225_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2225_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v_ctorInfo_2172_; lean_object* v_fieldInfo_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2224_; 
v_ctorInfo_2172_ = lean_ctor_get(v_a_2163_, 0);
v_fieldInfo_2173_ = lean_ctor_get(v_a_2163_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_a_2163_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2175_ = v_a_2163_;
v_isShared_2176_ = v_isSharedCheck_2224_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_fieldInfo_2173_);
lean_inc(v_ctorInfo_2172_);
lean_dec(v_a_2163_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2224_;
goto v_resetjp_2174_;
}
v___jp_2167_:
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v___x_2168_);
v___x_2170_ = v___x_2165_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2177_ = lean_array_get_size(v_a_1977_);
v___x_2178_ = l_Array_extract___redArg(v_a_1977_, v_numParams_2072_, v___x_2177_);
lean_dec(v_a_1977_);
v___x_2179_ = lean_array_get_size(v___x_2178_);
v___x_2180_ = lean_array_get_size(v_fieldInfo_2173_);
v___x_2181_ = lean_nat_dec_eq(v___x_2179_, v___x_2180_);
if (v___x_2181_ == 0)
{
lean_dec_ref(v___x_2178_);
lean_del_object(v___x_2175_);
lean_dec_ref(v_fieldInfo_2173_);
lean_dec_ref(v_ctorInfo_2172_);
lean_del_object(v___x_1643_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
goto v___jp_2167_;
}
else
{
if (v___x_2161_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_del_object(v___x_2165_);
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_2184_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_2180_, v_fieldInfo_2173_, v___x_2178_, v___x_2182_, v___x_2183_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2186_; lean_object* v_lctx_2187_; lean_object* v_nextIdx_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2215_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
v___x_2186_ = lean_st_ref_take(v_a_1624_);
v_lctx_2187_ = lean_ctor_get(v___x_2186_, 0);
v_nextIdx_2188_ = lean_ctor_get(v___x_2186_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2190_ = v___x_2186_;
v_isShared_2191_ = v_isSharedCheck_2215_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_nextIdx_2188_);
lean_inc(v_lctx_2187_);
lean_dec(v___x_2186_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2215_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; uint8_t v___x_2193_; lean_object* v___x_2195_; 
v___x_2192_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_ctorInfo_2172_);
v___x_2193_ = 1;
lean_inc_ref(v_ctorInfo_2172_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set_tag(v___x_2175_, 5);
lean_ctor_set(v___x_2175_, 1, v_a_2185_);
v___x_2195_ = v___x_2175_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_ctorInfo_2172_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_a_2185_);
v___x_2195_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2199_; 
lean_inc(v_binderName_1638_);
lean_inc(v_fvarId_1637_);
v___x_2196_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2196_, 0, v_fvarId_1637_);
lean_ctor_set(v___x_2196_, 1, v_binderName_1638_);
lean_ctor_set(v___x_2196_, 2, v___x_2192_);
lean_ctor_set(v___x_2196_, 3, v___x_2195_);
lean_inc_ref(v___x_2196_);
v___x_2197_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2193_, v_lctx_2187_, v___x_2196_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2197_);
v___x_2199_ = v___x_2190_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_nextIdx_2188_);
v___x_2199_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_st_ref_put(v_a_1624_, v___x_2199_);
v___x_2201_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_1620_, v_k_1621_, v_ctorInfo_2172_, v_fieldInfo_2173_, v___x_2178_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
lean_dec_ref(v___x_2178_);
lean_dec_ref(v_fieldInfo_2173_);
lean_dec_ref(v_ctorInfo_2172_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2212_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2212_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2212_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 1, v_a_2202_);
lean_ctor_set(v___x_1643_, 0, v___x_2196_);
v___x_2207_ = v___x_1643_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2209_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2207_);
v___x_2209_ = v___x_2204_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2196_, 4);
lean_del_object(v___x_1643_);
return v___x_2201_;
}
}
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref(v___x_2178_);
lean_del_object(v___x_2175_);
lean_dec_ref(v_fieldInfo_2173_);
lean_dec_ref(v_ctorInfo_2172_);
lean_del_object(v___x_1643_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
v_a_2216_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2184_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2184_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_dec_ref(v___x_2178_);
lean_del_object(v___x_2175_);
lean_dec_ref(v_fieldInfo_2173_);
lean_dec_ref(v_ctorInfo_2172_);
lean_del_object(v___x_1643_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
goto v___jp_2167_;
}
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_numParams_2072_);
lean_dec(v_a_1977_);
lean_del_object(v___x_1643_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
v_a_2226_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2162_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2162_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2245_; 
lean_inc(v_binderName_1638_);
lean_inc(v_fvarId_1637_);
lean_dec(v_numParams_2072_);
lean_dec(v_a_1977_);
lean_dec(v_declName_1972_);
lean_del_object(v___x_1643_);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_decl_1620_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; lean_object* v_unused_2247_; lean_object* v_unused_2248_; lean_object* v_unused_2249_; 
v_unused_2246_ = lean_ctor_get(v_decl_1620_, 3);
lean_dec(v_unused_2246_);
v_unused_2247_ = lean_ctor_get(v_decl_1620_, 2);
lean_dec(v_unused_2247_);
v_unused_2248_ = lean_ctor_get(v_decl_1620_, 1);
lean_dec(v_unused_2248_);
v_unused_2249_ = lean_ctor_get(v_decl_1620_, 0);
lean_dec(v_unused_2249_);
v___x_2235_ = v_decl_1620_;
v_isShared_2236_ = v_isSharedCheck_2245_;
goto v_resetjp_2234_;
}
else
{
lean_dec(v_decl_1620_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2245_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2237_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_2160_, v_cidx_2071_);
lean_dec(v_cidx_2071_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set_tag(v___x_2068_, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2237_);
v___x_2239_ = v___x_2068_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2241_; 
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 3, v___x_2239_);
lean_ctor_set(v___x_2235_, 2, v_a_2160_);
v___x_2241_ = v___x_2235_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_fvarId_1637_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_binderName_1638_);
lean_ctor_set(v_reuseFailAlloc_2243_, 2, v_a_2160_);
lean_ctor_set(v_reuseFailAlloc_2243_, 3, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
lean_object* v___x_2242_; 
v___x_2242_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1621_, v___x_2241_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_2242_;
}
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec(v_numParams_2072_);
lean_dec(v_cidx_2071_);
lean_del_object(v___x_2068_);
lean_dec(v_a_1977_);
lean_dec(v_declName_1972_);
lean_del_object(v___x_1643_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
v_a_2250_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2159_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2159_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v_numParams_2072_);
lean_dec(v_cidx_2071_);
lean_dec(v_induct_2070_);
lean_del_object(v___x_2068_);
lean_dec(v_a_1977_);
lean_dec_ref(v_args_1973_);
lean_dec(v_declName_1972_);
lean_del_object(v___x_1643_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
v_a_2258_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2073_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2073_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
case 7:
{
lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2282_; 
lean_dec(v_a_1977_);
lean_dec_ref(v_args_1973_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_val_1997_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; 
v_unused_2283_ = lean_ctor_get(v_val_1997_, 0);
lean_dec(v_unused_2283_);
v___x_2268_ = v_val_1997_;
v_isShared_2269_ = v_isSharedCheck_2282_;
goto v_resetjp_2267_;
}
else
{
lean_dec(v_val_1997_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2282_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2270_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11));
v___x_2271_ = l_Lean_Name_toString(v_declName_1972_, v___x_1646_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set_tag(v___x_2268_, 3);
lean_ctor_set(v___x_2268_, 0, v___x_2271_);
v___x_2273_ = v___x_2268_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2275_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 5);
lean_ctor_set(v___x_1643_, 1, v___x_2273_);
lean_ctor_set(v___x_1643_, 0, v___x_2270_);
v___x_2275_ = v___x_1643_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2276_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13));
v___x_2277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2275_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = l_Lean_MessageData_ofFormat(v___x_2277_);
v___x_2279_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2278_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_2279_;
}
}
}
}
default: 
{
lean_object* v___x_2284_; 
lean_dec(v_val_1997_);
lean_dec_ref(v_args_1973_);
lean_del_object(v___x_1643_);
v___x_2284_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1620_, v_k_1621_, v_declName_1972_, v_a_1977_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_2284_;
}
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec(v_a_1977_);
lean_dec_ref(v_args_1973_);
lean_dec(v_declName_1972_);
lean_del_object(v___x_1643_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
v_a_2285_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_1984_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_1984_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_a_1977_);
lean_dec_ref(v_args_1973_);
lean_dec(v_declName_1972_);
lean_del_object(v___x_1643_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
v_a_2293_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_1978_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_1978_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec_ref(v_args_1973_);
lean_dec(v_declName_1972_);
lean_del_object(v___x_1643_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_decl_1620_);
v_a_2301_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_1976_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_1976_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
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
default: 
{
lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2348_; 
lean_inc_ref(v_type_1639_);
lean_inc(v_binderName_1638_);
lean_inc(v_fvarId_1637_);
lean_del_object(v___x_1643_);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_decl_1620_);
if (v_isSharedCheck_2348_ == 0)
{
lean_object* v_unused_2349_; lean_object* v_unused_2350_; lean_object* v_unused_2351_; lean_object* v_unused_2352_; 
v_unused_2349_ = lean_ctor_get(v_decl_1620_, 3);
lean_dec(v_unused_2349_);
v_unused_2350_ = lean_ctor_get(v_decl_1620_, 2);
lean_dec(v_unused_2350_);
v_unused_2351_ = lean_ctor_get(v_decl_1620_, 1);
lean_dec(v_unused_2351_);
v_unused_2352_ = lean_ctor_get(v_decl_1620_, 0);
lean_dec(v_unused_2352_);
v___x_2310_ = v_decl_1620_;
v_isShared_2311_ = v_isSharedCheck_2348_;
goto v_resetjp_2309_;
}
else
{
lean_dec(v_decl_1620_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2348_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_fvarId_2312_; lean_object* v_args_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2347_; 
v_fvarId_2312_ = lean_ctor_get(v___x_1647_, 0);
v_args_2313_ = lean_ctor_get(v___x_1647_, 1);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2315_ = v___x_1647_;
v_isShared_2316_ = v_isSharedCheck_2347_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_args_2313_);
lean_inc(v_fvarId_2312_);
lean_dec(v___x_1647_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2347_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
size_t v_sz_2317_; size_t v___x_2318_; lean_object* v___x_2319_; 
v_sz_2317_ = lean_array_size(v_args_2313_);
v___x_2318_ = ((size_t)0ULL);
v___x_2319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_2317_, v___x_2318_, v_args_2313_, v_a_1622_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2321_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v___x_2321_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1639_, v_a_1625_, v_a_1626_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_2322_);
lean_dec(v_a_2322_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 1, v_a_2320_);
v___x_2325_ = v___x_2315_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_fvarId_2312_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2327_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 3, v___x_2325_);
lean_ctor_set(v___x_2310_, 2, v___x_2323_);
v___x_2327_ = v___x_2310_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_fvarId_1637_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_binderName_1638_);
lean_ctor_set(v_reuseFailAlloc_2329_, 2, v___x_2323_);
lean_ctor_set(v_reuseFailAlloc_2329_, 3, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2328_; 
v___x_2328_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1621_, v___x_2327_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_2328_;
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec(v_a_2320_);
lean_del_object(v___x_2315_);
lean_dec(v_fvarId_2312_);
lean_del_object(v___x_2310_);
lean_dec(v_binderName_1638_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1621_);
v_a_2331_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2321_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2321_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_del_object(v___x_2315_);
lean_dec(v_fvarId_2312_);
lean_del_object(v___x_2310_);
lean_dec_ref(v_type_1639_);
lean_dec(v_binderName_1638_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1621_);
v_a_2339_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2319_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2319_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
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
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2357_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1));
v___x_2358_ = lean_unsigned_to_nat(15u);
v___x_2359_ = lean_unsigned_to_nat(272u);
v___x_2360_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2361_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2362_ = l_mkPanicMessageWithDecl(v___x_2361_, v___x_2360_, v___x_2359_, v___x_2358_, v___x_2357_);
return v___x_2362_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2366_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5));
v___x_2367_ = lean_unsigned_to_nat(6u);
v___x_2368_ = lean_unsigned_to_nat(251u);
v___x_2369_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2370_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2371_ = l_mkPanicMessageWithDecl(v___x_2370_, v___x_2369_, v___x_2368_, v___x_2367_, v___x_2366_);
return v___x_2371_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7(void){
_start:
{
uint8_t v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = 0;
v___x_2373_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_2372_);
return v___x_2373_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2375_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8));
v___x_2376_ = lean_unsigned_to_nat(6u);
v___x_2377_ = lean_unsigned_to_nat(253u);
v___x_2378_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2379_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2380_ = l_mkPanicMessageWithDecl(v___x_2379_, v___x_2378_, v___x_2377_, v___x_2376_, v___x_2375_);
return v___x_2380_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10));
v___x_2383_ = lean_unsigned_to_nat(6u);
v___x_2384_ = lean_unsigned_to_nat(254u);
v___x_2385_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2386_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2387_ = l_mkPanicMessageWithDecl(v___x_2386_, v___x_2385_, v___x_2384_, v___x_2383_, v___x_2382_);
return v___x_2387_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2389_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12));
v___x_2390_ = lean_unsigned_to_nat(45u);
v___x_2391_ = lean_unsigned_to_nat(252u);
v___x_2392_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_2393_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2394_ = l_mkPanicMessageWithDecl(v___x_2393_, v___x_2392_, v___x_2391_, v___x_2390_, v___x_2389_);
return v___x_2394_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2397_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1));
v___x_2398_ = lean_unsigned_to_nat(18u);
v___x_2399_ = lean_unsigned_to_nat(293u);
v___x_2400_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0));
v___x_2401_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_2402_ = l_mkPanicMessageWithDecl(v___x_2401_, v___x_2400_, v___x_2399_, v___x_2398_, v___x_2397_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object* v_discr_2403_, lean_object* v_k_2404_, lean_object* v_ctorInfo_2405_, lean_object* v_params_2406_, lean_object* v_fields_2407_, lean_object* v_i_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v_jpParamMask_2424_; lean_object* v___y_2425_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v_i_2440_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v_i_2463_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2562_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2568_ = lean_array_get_size(v_params_2406_);
v___x_2569_ = lean_nat_dec_lt(v_i_2408_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; 
v___x_2570_ = lean_box(0);
v___y_2562_ = v___x_2570_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = lean_array_fget_borrowed(v_params_2406_, v_i_2408_);
lean_inc(v___x_2571_);
v___x_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
v___y_2562_ = v___x_2572_;
goto v___jp_2561_;
}
v___jp_2415_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2);
v___x_2422_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2421_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
return v___x_2422_;
}
v___jp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___y_2425_);
lean_ctor_set(v___x_2426_, 1, v_jpParamMask_2424_);
v___x_2427_ = lean_st_ref_put(v_a_2409_, v___x_2426_);
v___x_2428_ = lean_unsigned_to_nat(1u);
v___x_2429_ = lean_nat_add(v_i_2408_, v___x_2428_);
lean_dec(v_i_2408_);
v_i_2408_ = v___x_2429_;
goto _start;
}
v___jp_2431_:
{
lean_object* v_jpParamMask_2434_; 
v_jpParamMask_2434_ = lean_ctor_get(v___y_2432_, 1);
lean_inc_ref(v_jpParamMask_2434_);
lean_dec_ref(v___y_2432_);
v_jpParamMask_2424_ = v_jpParamMask_2434_;
v___y_2425_ = v___y_2433_;
goto v___jp_2423_;
}
v___jp_2435_:
{
lean_object* v_size_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v_size_2441_ = lean_ctor_get(v___y_2439_, 0);
v___x_2442_ = lean_unsigned_to_nat(1u);
v___x_2443_ = lean_nat_add(v_size_2441_, v___x_2442_);
v___x_2444_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2439_, v___x_2443_, v_i_2440_, v___y_2438_, v___y_2436_);
lean_dec(v_i_2440_);
v___y_2432_ = v___y_2437_;
v___y_2433_ = v___x_2444_;
goto v___jp_2431_;
}
v___jp_2445_:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___y_2449_, v___y_2448_);
switch(lean_obj_tag(v___x_2450_))
{
case 0:
{
lean_object* v_index_2451_; lean_object* v_size_2452_; lean_object* v___x_2453_; 
v_index_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_index_2451_);
lean_dec_ref_known(v___x_2450_, 3);
v_size_2452_ = lean_ctor_get(v___y_2449_, 0);
lean_inc(v_size_2452_);
v___x_2453_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2449_, v_size_2452_, v_index_2451_, v___y_2448_, v___y_2446_);
lean_dec(v_index_2451_);
v___y_2432_ = v___y_2447_;
v___y_2433_ = v___x_2453_;
goto v___jp_2431_;
}
case 1:
{
lean_object* v_index_2454_; 
v_index_2454_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_index_2454_);
lean_dec_ref_known(v___x_2450_, 1);
v___y_2436_ = v___y_2446_;
v___y_2437_ = v___y_2447_;
v___y_2438_ = v___y_2448_;
v___y_2439_ = v___y_2449_;
v_i_2440_ = v_index_2454_;
goto v___jp_2435_;
}
default: 
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = lean_unsigned_to_nat(0u);
v___x_2456_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2449_, v___x_2455_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_index_2457_; 
v_index_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_index_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v___y_2436_ = v___y_2446_;
v___y_2437_ = v___y_2447_;
v___y_2438_ = v___y_2448_;
v___y_2439_ = v___y_2449_;
v_i_2440_ = v_index_2457_;
goto v___jp_2435_;
}
else
{
lean_dec(v___y_2448_);
lean_dec(v___y_2446_);
v___y_2432_ = v___y_2447_;
v___y_2433_ = v___y_2449_;
goto v___jp_2431_;
}
}
}
}
v___jp_2458_:
{
lean_object* v_size_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_size_2464_ = lean_ctor_get(v___y_2461_, 0);
v___x_2465_ = lean_unsigned_to_nat(1u);
v___x_2466_ = lean_nat_add(v_size_2464_, v___x_2465_);
v___x_2467_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2461_, v___x_2466_, v_i_2463_, v___y_2462_, v___y_2459_);
lean_dec(v_i_2463_);
v___y_2432_ = v___y_2460_;
v___y_2433_ = v___x_2467_;
goto v___jp_2431_;
}
v___jp_2468_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v___y_2470_);
lean_dec_ref(v___y_2470_);
v___x_2474_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___x_2473_, v___y_2472_);
switch(lean_obj_tag(v___x_2474_))
{
case 0:
{
lean_object* v_index_2475_; lean_object* v_size_2476_; lean_object* v___x_2477_; 
v_index_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_index_2475_);
lean_dec_ref_known(v___x_2474_, 3);
v_size_2476_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_size_2476_);
v___x_2477_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2473_, v_size_2476_, v_index_2475_, v___y_2472_, v___y_2469_);
lean_dec(v_index_2475_);
v___y_2432_ = v___y_2471_;
v___y_2433_ = v___x_2477_;
goto v___jp_2431_;
}
case 1:
{
lean_object* v_index_2478_; 
v_index_2478_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_index_2478_);
lean_dec_ref_known(v___x_2474_, 1);
v___y_2459_ = v___y_2469_;
v___y_2460_ = v___y_2471_;
v___y_2461_ = v___x_2473_;
v___y_2462_ = v___y_2472_;
v_i_2463_ = v_index_2478_;
goto v___jp_2458_;
}
default: 
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = lean_unsigned_to_nat(0u);
v___x_2480_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2473_, v___x_2479_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_index_2481_; 
v_index_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_index_2481_);
lean_dec_ref_known(v___x_2480_, 1);
v___y_2459_ = v___y_2469_;
v___y_2460_ = v___y_2471_;
v___y_2461_ = v___x_2473_;
v___y_2462_ = v___y_2472_;
v_i_2463_ = v_index_2481_;
goto v___jp_2458_;
}
else
{
lean_dec(v___y_2472_);
lean_dec(v___y_2469_);
v___y_2432_ = v___y_2471_;
v___y_2433_ = v___x_2473_;
goto v___jp_2431_;
}
}
}
}
v___jp_2482_:
{
if (lean_obj_tag(v___y_2483_) == 0)
{
lean_dec(v_i_2408_);
lean_dec(v_discr_2403_);
if (lean_obj_tag(v___y_2484_) == 0)
{
lean_object* v___x_2485_; 
v___x_2485_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2404_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2485_;
}
else
{
lean_dec(v___y_2484_);
lean_dec_ref(v_k_2404_);
v___y_2416_ = v_a_2409_;
v___y_2417_ = v_a_2410_;
v___y_2418_ = v_a_2411_;
v___y_2419_ = v_a_2412_;
v___y_2420_ = v_a_2413_;
goto v___jp_2415_;
}
}
else
{
if (lean_obj_tag(v___y_2484_) == 1)
{
lean_object* v_val_2486_; lean_object* v_val_2487_; lean_object* v___x_2488_; lean_object* v_fst_2489_; 
v_val_2486_ = lean_ctor_get(v___y_2483_, 0);
lean_inc(v_val_2486_);
lean_dec_ref_known(v___y_2483_, 1);
v_val_2487_ = lean_ctor_get(v___y_2484_, 0);
lean_inc(v_val_2487_);
lean_dec_ref_known(v___y_2484_, 1);
lean_inc(v_discr_2403_);
v___x_2488_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_discr_2403_, v_ctorInfo_2405_, v_val_2487_);
v_fst_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_fst_2489_);
if (lean_obj_tag(v_fst_2489_) == 1)
{
lean_object* v___x_2490_; lean_object* v_fvarId_2491_; lean_object* v_subst_2492_; lean_object* v_jpParamMask_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
lean_dec_ref(v___x_2488_);
v___x_2490_ = lean_st_ref_take(v_a_2409_);
v_fvarId_2491_ = lean_ctor_get(v_val_2486_, 0);
lean_inc(v_fvarId_2491_);
lean_dec(v_val_2486_);
v_subst_2492_ = lean_ctor_get(v___x_2490_, 0);
lean_inc_ref(v_subst_2492_);
v_jpParamMask_2493_ = lean_ctor_get(v___x_2490_, 1);
lean_inc_ref(v_jpParamMask_2493_);
v___x_2494_ = lean_box(0);
v___x_2495_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_2492_, v_fvarId_2491_);
switch(lean_obj_tag(v___x_2495_))
{
case 0:
{
lean_object* v_index_2496_; lean_object* v_size_2497_; lean_object* v___x_2498_; 
lean_dec(v___x_2490_);
v_index_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_index_2496_);
lean_dec_ref_known(v___x_2495_, 3);
v_size_2497_ = lean_ctor_get(v_subst_2492_, 0);
lean_inc(v_size_2497_);
v___x_2498_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_2492_, v_size_2497_, v_index_2496_, v_fvarId_2491_, v___x_2494_);
lean_dec(v_index_2496_);
v_jpParamMask_2424_ = v_jpParamMask_2493_;
v___y_2425_ = v___x_2498_;
goto v___jp_2423_;
}
case 1:
{
lean_object* v_index_2499_; lean_object* v_size_2500_; lean_object* v_keyArray_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; 
v_index_2499_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_index_2499_);
lean_dec_ref_known(v___x_2495_, 1);
v_size_2500_ = lean_ctor_get(v_subst_2492_, 0);
v_keyArray_2501_ = lean_ctor_get(v_subst_2492_, 1);
v___x_2502_ = lean_unsigned_to_nat(1u);
v___x_2503_ = lean_nat_add(v_size_2500_, v___x_2502_);
v___x_2504_ = lean_array_get_size(v_keyArray_2501_);
v___x_2505_ = lean_nat_dec_lt(v___x_2503_, v___x_2504_);
if (v___x_2505_ == 0)
{
lean_dec(v___x_2503_);
lean_dec(v_index_2499_);
lean_dec_ref(v_jpParamMask_2493_);
v___y_2469_ = v___x_2494_;
v___y_2470_ = v_subst_2492_;
v___y_2471_ = v___x_2490_;
v___y_2472_ = v_fvarId_2491_;
goto v___jp_2468_;
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v___x_2506_ = lean_unsigned_to_nat(4u);
v___x_2507_ = lean_nat_mul(v___x_2503_, v___x_2506_);
v___x_2508_ = lean_unsigned_to_nat(3u);
v___x_2509_ = lean_nat_mul(v___x_2504_, v___x_2508_);
v___x_2510_ = lean_nat_dec_le(v___x_2507_, v___x_2509_);
lean_dec(v___x_2509_);
lean_dec(v___x_2507_);
if (v___x_2510_ == 0)
{
lean_dec(v___x_2503_);
lean_dec(v_index_2499_);
lean_dec_ref(v_jpParamMask_2493_);
v___y_2469_ = v___x_2494_;
v___y_2470_ = v_subst_2492_;
v___y_2471_ = v___x_2490_;
v___y_2472_ = v_fvarId_2491_;
goto v___jp_2468_;
}
else
{
lean_object* v___x_2511_; 
lean_dec(v___x_2490_);
v___x_2511_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_2492_, v___x_2503_, v_index_2499_, v_fvarId_2491_, v___x_2494_);
lean_dec(v_index_2499_);
v_jpParamMask_2424_ = v_jpParamMask_2493_;
v___y_2425_ = v___x_2511_;
goto v___jp_2423_;
}
}
}
default: 
{
lean_object* v_size_2512_; lean_object* v_keyArray_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
lean_dec_ref(v_jpParamMask_2493_);
v_size_2512_ = lean_ctor_get(v_subst_2492_, 0);
v_keyArray_2513_ = lean_ctor_get(v_subst_2492_, 1);
v___x_2514_ = lean_unsigned_to_nat(1u);
v___x_2515_ = lean_nat_add(v_size_2512_, v___x_2514_);
v___x_2516_ = lean_array_get_size(v_keyArray_2513_);
v___x_2517_ = lean_nat_dec_lt(v___x_2515_, v___x_2516_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; 
lean_dec(v___x_2515_);
v___x_2518_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_2492_);
lean_dec_ref(v_subst_2492_);
v___y_2446_ = v___x_2494_;
v___y_2447_ = v___x_2490_;
v___y_2448_ = v_fvarId_2491_;
v___y_2449_ = v___x_2518_;
goto v___jp_2445_;
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v___x_2519_ = lean_unsigned_to_nat(4u);
v___x_2520_ = lean_nat_mul(v___x_2515_, v___x_2519_);
lean_dec(v___x_2515_);
v___x_2521_ = lean_unsigned_to_nat(3u);
v___x_2522_ = lean_nat_mul(v___x_2516_, v___x_2521_);
v___x_2523_ = lean_nat_dec_le(v___x_2520_, v___x_2522_);
lean_dec(v___x_2522_);
lean_dec(v___x_2520_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_subst_2492_);
lean_dec_ref(v_subst_2492_);
v___y_2446_ = v___x_2494_;
v___y_2447_ = v___x_2490_;
v___y_2448_ = v_fvarId_2491_;
v___y_2449_ = v___x_2524_;
goto v___jp_2445_;
}
else
{
v___y_2446_ = v___x_2494_;
v___y_2447_ = v___x_2490_;
v___y_2448_ = v_fvarId_2491_;
v___y_2449_ = v_subst_2492_;
goto v___jp_2445_;
}
}
}
}
}
else
{
lean_object* v_snd_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2559_; 
v_snd_2525_ = lean_ctor_get(v___x_2488_, 1);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v___x_2488_, 0);
lean_dec(v_unused_2560_);
v___x_2527_ = v___x_2488_;
v_isShared_2528_ = v_isSharedCheck_2559_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_snd_2525_);
lean_dec(v___x_2488_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2559_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v_fvarId_2530_; lean_object* v_binderName_2531_; lean_object* v_lctx_2532_; lean_object* v_nextIdx_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2558_; 
v___x_2529_ = lean_st_ref_take(v_a_2411_);
v_fvarId_2530_ = lean_ctor_get(v_val_2486_, 0);
lean_inc(v_fvarId_2530_);
v_binderName_2531_ = lean_ctor_get(v_val_2486_, 1);
lean_inc(v_binderName_2531_);
lean_dec(v_val_2486_);
v_lctx_2532_ = lean_ctor_get(v___x_2529_, 0);
v_nextIdx_2533_ = lean_ctor_get(v___x_2529_, 1);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2535_ = v___x_2529_;
v_isShared_2536_ = v_isSharedCheck_2558_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_nextIdx_2533_);
lean_inc(v_lctx_2532_);
lean_dec(v___x_2529_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2558_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
uint8_t v___x_2537_; lean_object* v_decl_2538_; lean_object* v___x_2539_; lean_object* v___x_2541_; 
v___x_2537_ = 1;
v_decl_2538_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_2538_, 0, v_fvarId_2530_);
lean_ctor_set(v_decl_2538_, 1, v_binderName_2531_);
lean_ctor_set(v_decl_2538_, 2, v_snd_2525_);
lean_ctor_set(v_decl_2538_, 3, v_fst_2489_);
lean_inc_ref(v_decl_2538_);
v___x_2539_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2537_, v_lctx_2532_, v_decl_2538_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2539_);
v___x_2541_ = v___x_2535_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_nextIdx_2533_);
v___x_2541_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2542_ = lean_st_ref_put(v_a_2411_, v___x_2541_);
v___x_2543_ = lean_unsigned_to_nat(1u);
v___x_2544_ = lean_nat_add(v_i_2408_, v___x_2543_);
lean_dec(v_i_2408_);
v___x_2545_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2403_, v_k_2404_, v_ctorInfo_2405_, v_params_2406_, v_fields_2407_, v___x_2544_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2556_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2556_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2556_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 1, v_a_2546_);
lean_ctor_set(v___x_2527_, 0, v_decl_2538_);
v___x_2551_ = v___x_2527_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_decl_2538_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2553_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2551_);
v___x_2553_ = v___x_2548_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
else
{
lean_dec_ref_known(v_decl_2538_, 4);
lean_del_object(v___x_2527_);
return v___x_2545_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___y_2483_, 1);
lean_dec(v___y_2484_);
lean_dec(v_i_2408_);
lean_dec_ref(v_k_2404_);
lean_dec(v_discr_2403_);
v___y_2416_ = v_a_2409_;
v___y_2417_ = v_a_2410_;
v___y_2418_ = v_a_2411_;
v___y_2419_ = v_a_2412_;
v___y_2420_ = v_a_2413_;
goto v___jp_2415_;
}
}
}
v___jp_2561_:
{
lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2563_ = lean_array_get_size(v_fields_2407_);
v___x_2564_ = lean_nat_dec_lt(v_i_2408_, v___x_2563_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; 
v___x_2565_ = lean_box(0);
v___y_2483_ = v___y_2562_;
v___y_2484_ = v___x_2565_;
goto v___jp_2482_;
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = lean_array_fget_borrowed(v_fields_2407_, v_i_2408_);
lean_inc(v___x_2566_);
v___x_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
v___y_2483_ = v___y_2562_;
v___y_2484_ = v___x_2567_;
goto v___jp_2482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(lean_object* v_discr_2573_, lean_object* v_alt_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
if (lean_obj_tag(v_alt_2574_) == 0)
{
lean_object* v_ctorName_2581_; lean_object* v_params_2582_; lean_object* v_code_2583_; lean_object* v___x_2584_; 
v_ctorName_2581_ = lean_ctor_get(v_alt_2574_, 0);
lean_inc(v_ctorName_2581_);
v_params_2582_ = lean_ctor_get(v_alt_2574_, 1);
lean_inc_ref(v_params_2582_);
v_code_2583_ = lean_ctor_get(v_alt_2574_, 2);
lean_inc_ref(v_code_2583_);
lean_dec_ref_known(v_alt_2574_, 3);
v___x_2584_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_2581_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v_ctorInfo_2586_; lean_object* v_fieldInfo_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2612_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v_ctorInfo_2586_ = lean_ctor_get(v_a_2585_, 0);
v_fieldInfo_2587_ = lean_ctor_get(v_a_2585_, 1);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_a_2585_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2589_ = v_a_2585_;
v_isShared_2590_ = v_isSharedCheck_2612_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_fieldInfo_2587_);
lean_inc(v_ctorInfo_2586_);
lean_dec(v_a_2585_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2612_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2573_, v_code_2583_, v_ctorInfo_2586_, v_params_2582_, v_fieldInfo_2587_, v___x_2591_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
lean_dec_ref(v_fieldInfo_2587_);
lean_dec_ref(v_params_2582_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2603_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2603_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2603_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set_tag(v___x_2589_, 1);
lean_ctor_set(v___x_2589_, 1, v_a_2593_);
v___x_2598_ = v___x_2589_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_ctorInfo_2586_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2600_; 
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2598_);
v___x_2600_ = v___x_2595_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_del_object(v___x_2589_);
lean_dec_ref(v_ctorInfo_2586_);
v_a_2604_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2592_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2592_);
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
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v_code_2583_);
lean_dec_ref(v_params_2582_);
lean_dec(v_discr_2573_);
v_a_2613_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2584_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2584_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_code_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_discr_2573_);
v_code_2621_ = lean_ctor_get(v_alt_2574_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_alt_2574_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2623_ = v_alt_2574_;
v_isShared_2624_ = v_isSharedCheck_2645_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_code_2621_);
lean_dec(v_alt_2574_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2645_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; 
v___x_2625_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_2621_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2636_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2636_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2636_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v_a_2626_);
v___x_2631_ = v___x_2623_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2633_; 
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_2631_);
v___x_2633_ = v___x_2628_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_del_object(v___x_2623_);
v_a_2637_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2625_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2625_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(lean_object* v_fvarId_2646_, size_t v_sz_2647_, size_t v_i_2648_, lean_object* v_bs_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
uint8_t v___x_2656_; 
v___x_2656_ = lean_usize_dec_lt(v_i_2648_, v_sz_2647_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; 
lean_dec(v_fvarId_2646_);
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_bs_2649_);
return v___x_2657_;
}
else
{
lean_object* v_v_2658_; lean_object* v___x_2659_; 
v_v_2658_ = lean_array_uget_borrowed(v_bs_2649_, v_i_2648_);
lean_inc(v_v_2658_);
lean_inc(v_fvarId_2646_);
v___x_2659_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_fvarId_2646_, v_v_2658_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; lean_object* v_bs_x27_2662_; size_t v___x_2663_; size_t v___x_2664_; lean_object* v___x_2665_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = lean_unsigned_to_nat(0u);
v_bs_x27_2662_ = lean_array_uset(v_bs_2649_, v_i_2648_, v___x_2661_);
v___x_2663_ = ((size_t)1ULL);
v___x_2664_ = lean_usize_add(v_i_2648_, v___x_2663_);
v___x_2665_ = lean_array_uset(v_bs_x27_2662_, v_i_2648_, v_a_2660_);
v_i_2648_ = v___x_2664_;
v_bs_2649_ = v___x_2665_;
goto _start;
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec_ref(v_bs_2649_);
lean_dec(v_fvarId_2646_);
v_a_2667_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2659_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2659_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(lean_object* v_c_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
switch(lean_obj_tag(v_c_2675_))
{
case 0:
{
lean_object* v_decl_2682_; lean_object* v_k_2683_; lean_object* v___x_2684_; 
v_decl_2682_ = lean_ctor_get(v_c_2675_, 0);
lean_inc_ref(v_decl_2682_);
v_k_2683_ = lean_ctor_get(v_c_2675_, 1);
lean_inc_ref(v_k_2683_);
lean_dec_ref_known(v_c_2675_, 2);
v___x_2684_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2682_, v_k_2683_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
return v___x_2684_;
}
case 1:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
lean_dec_ref_known(v_c_2675_, 2);
v___x_2685_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2);
v___x_2686_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2685_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
return v___x_2686_;
}
case 2:
{
lean_object* v_decl_2687_; lean_object* v_k_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2845_; 
v_decl_2687_ = lean_ctor_get(v_c_2675_, 0);
v_k_2688_ = lean_ctor_get(v_c_2675_, 1);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_c_2675_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2690_ = v_c_2675_;
v_isShared_2691_ = v_isSharedCheck_2845_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_k_2688_);
lean_inc(v_decl_2687_);
lean_dec(v_c_2675_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2845_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v_fvarId_2692_; lean_object* v_binderName_2693_; lean_object* v_params_2694_; lean_object* v_type_2695_; lean_object* v_value_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2844_; 
v_fvarId_2692_ = lean_ctor_get(v_decl_2687_, 0);
v_binderName_2693_ = lean_ctor_get(v_decl_2687_, 1);
v_params_2694_ = lean_ctor_get(v_decl_2687_, 2);
v_type_2695_ = lean_ctor_get(v_decl_2687_, 3);
v_value_2696_ = lean_ctor_get(v_decl_2687_, 4);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_decl_2687_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2698_ = v_decl_2687_;
v_isShared_2699_ = v_isSharedCheck_2844_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_value_2696_);
lean_inc(v_type_2695_);
lean_inc(v_params_2694_);
lean_inc(v_binderName_2693_);
lean_inc(v_fvarId_2692_);
lean_dec(v_decl_2687_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2844_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
size_t v_sz_2700_; size_t v___x_2701_; lean_object* v___x_2702_; 
v_sz_2700_ = lean_array_size(v_params_2694_);
v___x_2701_ = ((size_t)0ULL);
v___x_2702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2700_, v___x_2701_, v_params_2694_, v_a_2676_, v_a_2678_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___y_2705_; lean_object* v___x_2747_; lean_object* v_subst_2748_; lean_object* v_jpParamMask_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2835_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
v___x_2747_ = lean_st_ref_take(v_a_2676_);
v_subst_2748_ = lean_ctor_get(v___x_2747_, 0);
v_jpParamMask_2749_ = lean_ctor_get(v___x_2747_, 1);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2751_ = v___x_2747_;
v_isShared_2752_ = v_isSharedCheck_2835_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_jpParamMask_2749_);
lean_inc(v_subst_2748_);
lean_dec(v___x_2747_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2835_;
goto v_resetjp_2750_;
}
v___jp_2704_:
{
lean_object* v___x_2706_; 
v___x_2706_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_value_2696_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2708_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2706_, 1);
v___x_2708_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2688_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2708_, 1);
v___x_2710_ = lean_array_get_size(v_a_2703_);
lean_dec(v_a_2703_);
v___x_2711_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2695_, v___x_2710_, v_a_2679_, v_a_2680_);
lean_dec_ref(v_type_2695_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2738_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2738_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2738_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; lean_object* v_lctx_2717_; lean_object* v_nextIdx_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2737_; 
v___x_2716_ = lean_st_ref_take(v_a_2678_);
v_lctx_2717_ = lean_ctor_get(v___x_2716_, 0);
v_nextIdx_2718_ = lean_ctor_get(v___x_2716_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2720_ = v___x_2716_;
v_isShared_2721_ = v_isSharedCheck_2737_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_nextIdx_2718_);
lean_inc(v_lctx_2717_);
lean_dec(v___x_2716_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2737_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
uint8_t v___x_2722_; lean_object* v___x_2724_; 
v___x_2722_ = 1;
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 4, v_a_2707_);
lean_ctor_set(v___x_2698_, 3, v_a_2712_);
lean_ctor_set(v___x_2698_, 2, v___y_2705_);
v___x_2724_ = v___x_2698_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_fvarId_2692_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_binderName_2693_);
lean_ctor_set(v_reuseFailAlloc_2736_, 2, v___y_2705_);
lean_ctor_set(v_reuseFailAlloc_2736_, 3, v_a_2712_);
lean_ctor_set(v_reuseFailAlloc_2736_, 4, v_a_2707_);
v___x_2724_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_inc_ref(v___x_2724_);
v___x_2725_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2722_, v_lctx_2717_, v___x_2724_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2725_);
v___x_2727_ = v___x_2720_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2725_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_nextIdx_2718_);
v___x_2727_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2728_ = lean_st_ref_put(v_a_2678_, v___x_2727_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 1, v_a_2709_);
lean_ctor_set(v___x_2690_, 0, v___x_2724_);
v___x_2730_ = v___x_2690_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_a_2709_);
v___x_2730_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2732_; 
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2730_);
v___x_2732_ = v___x_2714_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2730_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_dec(v_a_2709_);
lean_dec(v_a_2707_);
lean_dec_ref(v___y_2705_);
lean_del_object(v___x_2698_);
lean_dec(v_binderName_2693_);
lean_dec(v_fvarId_2692_);
lean_del_object(v___x_2690_);
v_a_2739_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2711_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2711_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
else
{
lean_dec(v_a_2707_);
lean_dec_ref(v___y_2705_);
lean_dec(v_a_2703_);
lean_del_object(v___x_2698_);
lean_dec_ref(v_type_2695_);
lean_dec(v_binderName_2693_);
lean_dec(v_fvarId_2692_);
lean_del_object(v___x_2690_);
return v___x_2708_;
}
}
else
{
lean_dec_ref(v___y_2705_);
lean_dec(v_a_2703_);
lean_del_object(v___x_2698_);
lean_dec_ref(v_type_2695_);
lean_dec(v_binderName_2693_);
lean_dec(v_fvarId_2692_);
lean_del_object(v___x_2690_);
lean_dec_ref(v_k_2688_);
return v___x_2706_;
}
}
v_resetjp_2750_:
{
size_t v_sz_2753_; lean_object* v___x_2754_; lean_object* v___y_2756_; lean_object* v___y_2772_; lean_object* v_i_2773_; lean_object* v___y_2779_; lean_object* v___y_2789_; lean_object* v_i_2790_; lean_object* v___x_2805_; 
v_sz_2753_ = lean_array_size(v_a_2703_);
lean_inc(v_a_2703_);
v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_2753_, v___x_2701_, v_a_2703_);
v___x_2805_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_jpParamMask_2749_, v_fvarId_2692_);
switch(lean_obj_tag(v___x_2805_))
{
case 0:
{
lean_object* v_index_2806_; lean_object* v_size_2807_; lean_object* v___x_2808_; 
v_index_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_index_2806_);
lean_dec_ref_known(v___x_2805_, 3);
v_size_2807_ = lean_ctor_get(v_jpParamMask_2749_, 0);
lean_inc(v_size_2807_);
lean_inc_ref(v___x_2754_);
lean_inc(v_fvarId_2692_);
v___x_2808_ = l_Std_DHashMap_Raw_setEntry___redArg(v_jpParamMask_2749_, v_size_2807_, v_index_2806_, v_fvarId_2692_, v___x_2754_);
lean_dec(v_index_2806_);
v___y_2756_ = v___x_2808_;
goto v___jp_2755_;
}
case 1:
{
lean_object* v_index_2809_; lean_object* v_size_2810_; lean_object* v_keyArray_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; uint8_t v___x_2815_; 
v_index_2809_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_index_2809_);
lean_dec_ref_known(v___x_2805_, 1);
v_size_2810_ = lean_ctor_get(v_jpParamMask_2749_, 0);
v_keyArray_2811_ = lean_ctor_get(v_jpParamMask_2749_, 1);
v___x_2812_ = lean_unsigned_to_nat(1u);
v___x_2813_ = lean_nat_add(v_size_2810_, v___x_2812_);
v___x_2814_ = lean_array_get_size(v_keyArray_2811_);
v___x_2815_ = lean_nat_dec_lt(v___x_2813_, v___x_2814_);
if (v___x_2815_ == 0)
{
lean_dec(v___x_2813_);
lean_dec(v_index_2809_);
goto v___jp_2795_;
}
else
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; uint8_t v___x_2820_; 
v___x_2816_ = lean_unsigned_to_nat(4u);
v___x_2817_ = lean_nat_mul(v___x_2813_, v___x_2816_);
v___x_2818_ = lean_unsigned_to_nat(3u);
v___x_2819_ = lean_nat_mul(v___x_2814_, v___x_2818_);
v___x_2820_ = lean_nat_dec_le(v___x_2817_, v___x_2819_);
lean_dec(v___x_2819_);
lean_dec(v___x_2817_);
if (v___x_2820_ == 0)
{
lean_dec(v___x_2813_);
lean_dec(v_index_2809_);
goto v___jp_2795_;
}
else
{
lean_object* v___x_2821_; 
lean_inc_ref(v___x_2754_);
lean_inc(v_fvarId_2692_);
v___x_2821_ = l_Std_DHashMap_Raw_setEntry___redArg(v_jpParamMask_2749_, v___x_2813_, v_index_2809_, v_fvarId_2692_, v___x_2754_);
lean_dec(v_index_2809_);
v___y_2756_ = v___x_2821_;
goto v___jp_2755_;
}
}
}
default: 
{
lean_object* v_size_2822_; lean_object* v_keyArray_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v_size_2822_ = lean_ctor_get(v_jpParamMask_2749_, 0);
v_keyArray_2823_ = lean_ctor_get(v_jpParamMask_2749_, 1);
v___x_2824_ = lean_unsigned_to_nat(1u);
v___x_2825_ = lean_nat_add(v_size_2822_, v___x_2824_);
v___x_2826_ = lean_array_get_size(v_keyArray_2823_);
v___x_2827_ = lean_nat_dec_lt(v___x_2825_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; 
lean_dec(v___x_2825_);
v___x_2828_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_jpParamMask_2749_);
lean_dec_ref(v_jpParamMask_2749_);
v___y_2779_ = v___x_2828_;
goto v___jp_2778_;
}
else
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; uint8_t v___x_2833_; 
v___x_2829_ = lean_unsigned_to_nat(4u);
v___x_2830_ = lean_nat_mul(v___x_2825_, v___x_2829_);
lean_dec(v___x_2825_);
v___x_2831_ = lean_unsigned_to_nat(3u);
v___x_2832_ = lean_nat_mul(v___x_2826_, v___x_2831_);
v___x_2833_ = lean_nat_dec_le(v___x_2830_, v___x_2832_);
lean_dec(v___x_2832_);
lean_dec(v___x_2830_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_jpParamMask_2749_);
lean_dec_ref(v_jpParamMask_2749_);
v___y_2779_ = v___x_2834_;
goto v___jp_2778_;
}
else
{
v___y_2779_ = v_jpParamMask_2749_;
goto v___jp_2778_;
}
}
}
}
v___jp_2755_:
{
lean_object* v___x_2758_; 
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 1, v___y_2756_);
v___x_2758_ = v___x_2751_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_subst_2748_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v___y_2756_);
v___x_2758_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2759_ = lean_st_ref_put(v_a_2676_, v___x_2758_);
v___x_2760_ = lean_unsigned_to_nat(0u);
v___x_2761_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3));
v___x_2762_ = l_Array_zip___redArg(v_a_2703_, v___x_2754_);
lean_dec_ref(v___x_2754_);
v___x_2763_ = lean_array_get_size(v___x_2762_);
v___x_2764_ = lean_nat_dec_lt(v___x_2760_, v___x_2763_);
if (v___x_2764_ == 0)
{
lean_dec_ref(v___x_2762_);
v___y_2705_ = v___x_2761_;
goto v___jp_2704_;
}
else
{
uint8_t v___x_2765_; 
v___x_2765_ = lean_nat_dec_le(v___x_2763_, v___x_2763_);
if (v___x_2765_ == 0)
{
if (v___x_2764_ == 0)
{
lean_dec_ref(v___x_2762_);
v___y_2705_ = v___x_2761_;
goto v___jp_2704_;
}
else
{
size_t v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = lean_usize_of_nat(v___x_2763_);
v___x_2767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2762_, v___x_2701_, v___x_2766_, v___x_2761_);
lean_dec_ref(v___x_2762_);
v___y_2705_ = v___x_2767_;
goto v___jp_2704_;
}
}
else
{
size_t v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = lean_usize_of_nat(v___x_2763_);
v___x_2769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2762_, v___x_2701_, v___x_2768_, v___x_2761_);
lean_dec_ref(v___x_2762_);
v___y_2705_ = v___x_2769_;
goto v___jp_2704_;
}
}
}
}
v___jp_2771_:
{
lean_object* v_size_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v_size_2774_ = lean_ctor_get(v___y_2772_, 0);
v___x_2775_ = lean_unsigned_to_nat(1u);
v___x_2776_ = lean_nat_add(v_size_2774_, v___x_2775_);
lean_inc_ref(v___x_2754_);
lean_inc(v_fvarId_2692_);
v___x_2777_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2772_, v___x_2776_, v_i_2773_, v_fvarId_2692_, v___x_2754_);
lean_dec(v_i_2773_);
v___y_2756_ = v___x_2777_;
goto v___jp_2755_;
}
v___jp_2778_:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___y_2779_, v_fvarId_2692_);
switch(lean_obj_tag(v___x_2780_))
{
case 0:
{
lean_object* v_index_2781_; lean_object* v_size_2782_; lean_object* v___x_2783_; 
v_index_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_index_2781_);
lean_dec_ref_known(v___x_2780_, 3);
v_size_2782_ = lean_ctor_get(v___y_2779_, 0);
lean_inc(v_size_2782_);
lean_inc_ref(v___x_2754_);
lean_inc(v_fvarId_2692_);
v___x_2783_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2779_, v_size_2782_, v_index_2781_, v_fvarId_2692_, v___x_2754_);
lean_dec(v_index_2781_);
v___y_2756_ = v___x_2783_;
goto v___jp_2755_;
}
case 1:
{
lean_object* v_index_2784_; 
v_index_2784_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_index_2784_);
lean_dec_ref_known(v___x_2780_, 1);
v___y_2772_ = v___y_2779_;
v_i_2773_ = v_index_2784_;
goto v___jp_2771_;
}
default: 
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = lean_unsigned_to_nat(0u);
v___x_2786_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2779_, v___x_2785_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_index_2787_; 
v_index_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_index_2787_);
lean_dec_ref_known(v___x_2786_, 1);
v___y_2772_ = v___y_2779_;
v_i_2773_ = v_index_2787_;
goto v___jp_2771_;
}
else
{
v___y_2756_ = v___y_2779_;
goto v___jp_2755_;
}
}
}
}
v___jp_2788_:
{
lean_object* v_size_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_size_2791_ = lean_ctor_get(v___y_2789_, 0);
v___x_2792_ = lean_unsigned_to_nat(1u);
v___x_2793_ = lean_nat_add(v_size_2791_, v___x_2792_);
lean_inc_ref(v___x_2754_);
lean_inc(v_fvarId_2692_);
v___x_2794_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2789_, v___x_2793_, v_i_2790_, v_fvarId_2692_, v___x_2754_);
lean_dec(v_i_2790_);
v___y_2756_ = v___x_2794_;
goto v___jp_2755_;
}
v___jp_2795_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__1___redArg(v_jpParamMask_2749_);
lean_dec_ref(v_jpParamMask_2749_);
v___x_2797_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v___x_2796_, v_fvarId_2692_);
switch(lean_obj_tag(v___x_2797_))
{
case 0:
{
lean_object* v_index_2798_; lean_object* v_size_2799_; lean_object* v___x_2800_; 
v_index_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_index_2798_);
lean_dec_ref_known(v___x_2797_, 3);
v_size_2799_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_size_2799_);
lean_inc_ref(v___x_2754_);
lean_inc(v_fvarId_2692_);
v___x_2800_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2796_, v_size_2799_, v_index_2798_, v_fvarId_2692_, v___x_2754_);
lean_dec(v_index_2798_);
v___y_2756_ = v___x_2800_;
goto v___jp_2755_;
}
case 1:
{
lean_object* v_index_2801_; 
v_index_2801_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_index_2801_);
lean_dec_ref_known(v___x_2797_, 1);
v___y_2789_ = v___x_2796_;
v_i_2790_ = v_index_2801_;
goto v___jp_2788_;
}
default: 
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = lean_unsigned_to_nat(0u);
v___x_2803_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2796_, v___x_2802_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_index_2804_; 
v_index_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_index_2804_);
lean_dec_ref_known(v___x_2803_, 1);
v___y_2789_ = v___x_2796_;
v_i_2790_ = v_index_2804_;
goto v___jp_2788_;
}
else
{
v___y_2756_ = v___x_2796_;
goto v___jp_2755_;
}
}
}
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_del_object(v___x_2698_);
lean_dec_ref(v_value_2696_);
lean_dec_ref(v_type_2695_);
lean_dec(v_binderName_2693_);
lean_dec(v_fvarId_2692_);
lean_del_object(v___x_2690_);
lean_dec_ref(v_k_2688_);
v_a_2836_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2702_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2702_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2846_; lean_object* v_args_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2883_; 
v_fvarId_2846_ = lean_ctor_get(v_c_2675_, 0);
v_args_2847_ = lean_ctor_get(v_c_2675_, 1);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_c_2675_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2849_ = v_c_2675_;
v_isShared_2850_ = v_isSharedCheck_2883_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_args_2847_);
lean_inc(v_fvarId_2846_);
lean_dec(v_c_2675_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2883_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v_a_2852_; lean_object* v___y_2858_; lean_object* v___x_2868_; lean_object* v_jpParamMask_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2868_ = lean_st_ref_get(v_a_2676_);
v_jpParamMask_2869_ = lean_ctor_get(v___x_2868_, 1);
lean_inc_ref(v_jpParamMask_2869_);
lean_dec(v___x_2868_);
v___x_2870_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_jpParamMask_2869_, v_fvarId_2846_);
lean_dec_ref(v_jpParamMask_2869_);
v___x_2871_ = lean_unsigned_to_nat(0u);
v___x_2872_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_2873_ = l_Array_zip___redArg(v_args_2847_, v___x_2870_);
lean_dec_ref(v___x_2870_);
lean_dec_ref(v_args_2847_);
v___x_2874_ = lean_array_get_size(v___x_2873_);
v___x_2875_ = lean_nat_dec_lt(v___x_2871_, v___x_2874_);
if (v___x_2875_ == 0)
{
lean_dec_ref(v___x_2873_);
v_a_2852_ = v___x_2872_;
goto v___jp_2851_;
}
else
{
uint8_t v___x_2876_; 
v___x_2876_ = lean_nat_dec_le(v___x_2874_, v___x_2874_);
if (v___x_2876_ == 0)
{
if (v___x_2875_ == 0)
{
lean_dec_ref(v___x_2873_);
v_a_2852_ = v___x_2872_;
goto v___jp_2851_;
}
else
{
size_t v___x_2877_; size_t v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = ((size_t)0ULL);
v___x_2878_ = lean_usize_of_nat(v___x_2874_);
v___x_2879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2873_, v___x_2877_, v___x_2878_, v___x_2872_, v_a_2676_);
lean_dec_ref(v___x_2873_);
v___y_2858_ = v___x_2879_;
goto v___jp_2857_;
}
}
else
{
size_t v___x_2880_; size_t v___x_2881_; lean_object* v___x_2882_; 
v___x_2880_ = ((size_t)0ULL);
v___x_2881_ = lean_usize_of_nat(v___x_2874_);
v___x_2882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2873_, v___x_2880_, v___x_2881_, v___x_2872_, v_a_2676_);
lean_dec_ref(v___x_2873_);
v___y_2858_ = v___x_2882_;
goto v___jp_2857_;
}
}
v___jp_2851_:
{
lean_object* v___x_2854_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v_a_2852_);
v___x_2854_ = v___x_2849_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_fvarId_2846_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_a_2852_);
v___x_2854_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2855_; 
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
return v___x_2855_;
}
}
v___jp_2857_:
{
if (lean_obj_tag(v___y_2858_) == 0)
{
lean_object* v_a_2859_; 
v_a_2859_ = lean_ctor_get(v___y_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___y_2858_, 1);
v_a_2852_ = v_a_2859_;
goto v___jp_2851_;
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_del_object(v___x_2849_);
lean_dec(v_fvarId_2846_);
v_a_2860_ = lean_ctor_get(v___y_2858_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___y_2858_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___y_2858_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___y_2858_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
}
case 4:
{
lean_object* v_cases_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2994_; 
v_cases_2884_ = lean_ctor_get(v_c_2675_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_c_2675_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2886_ = v_c_2675_;
v_isShared_2887_ = v_isSharedCheck_2994_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_cases_2884_);
lean_dec(v_c_2675_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2994_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v_typeName_2888_; lean_object* v_resultType_2889_; lean_object* v_discr_2890_; lean_object* v_alts_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2993_; 
v_typeName_2888_ = lean_ctor_get(v_cases_2884_, 0);
v_resultType_2889_ = lean_ctor_get(v_cases_2884_, 1);
v_discr_2890_ = lean_ctor_get(v_cases_2884_, 2);
v_alts_2891_ = lean_ctor_get(v_cases_2884_, 3);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_cases_2884_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2893_ = v_cases_2884_;
v_isShared_2894_ = v_isSharedCheck_2993_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_alts_2891_);
lean_inc(v_discr_2890_);
lean_inc(v_resultType_2889_);
lean_inc(v_typeName_2888_);
lean_dec(v_cases_2884_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2993_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; 
lean_inc(v_typeName_2888_);
v___x_2895_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_2888_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___x_2895_, 1);
if (lean_obj_tag(v_a_2896_) == 1)
{
lean_object* v_val_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; uint8_t v___x_2900_; 
lean_del_object(v___x_2893_);
lean_dec_ref(v_resultType_2889_);
lean_dec(v_typeName_2888_);
lean_del_object(v___x_2886_);
v_val_2897_ = lean_ctor_get(v_a_2896_, 0);
lean_inc(v_val_2897_);
lean_dec_ref_known(v_a_2896_, 1);
v___x_2898_ = lean_array_get_size(v_alts_2891_);
v___x_2899_ = lean_unsigned_to_nat(1u);
v___x_2900_ = lean_nat_dec_eq(v___x_2898_, v___x_2899_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
lean_dec(v_val_2897_);
lean_dec_ref(v_alts_2891_);
lean_dec(v_discr_2890_);
v___x_2901_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6);
v___x_2902_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2901_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
return v___x_2902_;
}
else
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2903_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7);
v___x_2904_ = lean_unsigned_to_nat(0u);
v___x_2905_ = lean_array_get(v___x_2903_, v_alts_2891_, v___x_2904_);
lean_dec_ref(v_alts_2891_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_ctorName_2906_; lean_object* v_params_2907_; lean_object* v_code_2908_; lean_object* v_ctorName_2909_; lean_object* v_fieldIdx_2910_; uint8_t v___x_2911_; 
v_ctorName_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_ctorName_2906_);
v_params_2907_ = lean_ctor_get(v___x_2905_, 1);
lean_inc_ref(v_params_2907_);
v_code_2908_ = lean_ctor_get(v___x_2905_, 2);
lean_inc_ref(v_code_2908_);
lean_dec_ref_known(v___x_2905_, 3);
v_ctorName_2909_ = lean_ctor_get(v_val_2897_, 0);
lean_inc(v_ctorName_2909_);
v_fieldIdx_2910_ = lean_ctor_get(v_val_2897_, 2);
lean_inc(v_fieldIdx_2910_);
lean_dec(v_val_2897_);
v___x_2911_ = lean_name_eq(v_ctorName_2906_, v_ctorName_2909_);
lean_dec(v_ctorName_2909_);
lean_dec(v_ctorName_2906_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
lean_dec(v_fieldIdx_2910_);
lean_dec_ref(v_code_2908_);
lean_dec_ref(v_params_2907_);
lean_dec(v_discr_2890_);
v___x_2912_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9);
v___x_2913_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2912_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
return v___x_2913_;
}
else
{
lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = lean_array_get_size(v_params_2907_);
v___x_2915_ = lean_nat_dec_lt(v_fieldIdx_2910_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
lean_dec(v_fieldIdx_2910_);
lean_dec_ref(v_code_2908_);
lean_dec_ref(v_params_2907_);
lean_dec(v_discr_2890_);
v___x_2916_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11);
v___x_2917_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2916_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
return v___x_2917_;
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = lean_box(0);
v___x_2919_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v___x_2914_, v_params_2907_, v_fieldIdx_2910_, v_discr_2890_, v___x_2904_, v___x_2918_, v_a_2676_);
lean_dec(v_fieldIdx_2910_);
lean_dec_ref(v_params_2907_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_dec_ref_known(v___x_2919_, 1);
v_c_2675_ = v_code_2908_;
goto _start;
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec_ref(v_code_2908_);
v_a_2921_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2919_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2919_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
}
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec(v___x_2905_);
lean_dec(v_val_2897_);
lean_dec(v_discr_2890_);
v___x_2929_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13);
v___x_2930_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2929_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
return v___x_2930_;
}
}
}
else
{
lean_object* v___x_2931_; lean_object* v_subst_2932_; uint8_t v___x_2933_; lean_object* v___x_2934_; 
lean_dec(v_a_2896_);
v___x_2931_ = lean_st_ref_get(v_a_2676_);
v_subst_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc_ref(v_subst_2932_);
lean_dec(v___x_2931_);
v___x_2933_ = 1;
v___x_2934_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2932_, v_discr_2890_, v___x_2933_);
lean_dec_ref(v_subst_2932_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_fvarId_2935_; lean_object* v___x_2936_; 
v_fvarId_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_fvarId_2935_);
lean_dec_ref_known(v___x_2934_, 1);
v___x_2936_ = l_Lean_Compiler_LCNF_toImpureType(v_resultType_2889_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; size_t v_sz_2938_; size_t v___x_2939_; lean_object* v___x_2940_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
v_sz_2938_ = lean_array_size(v_alts_2891_);
v___x_2939_ = ((size_t)0ULL);
lean_inc(v_fvarId_2935_);
v___x_2940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2935_, v_sz_2938_, v___x_2939_, v_alts_2891_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2940_, 1);
v___x_2942_ = l_Lean_Compiler_LCNF_nameToImpureType(v_typeName_2888_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2958_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_2958_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2958_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2947_ = l_Lean_Expr_getAppFn(v_a_2943_);
lean_dec(v_a_2943_);
v___x_2948_ = l_Lean_Expr_constName_x21(v___x_2947_);
lean_dec_ref(v___x_2947_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 3, v_a_2941_);
lean_ctor_set(v___x_2893_, 2, v_fvarId_2935_);
lean_ctor_set(v___x_2893_, 1, v_a_2937_);
lean_ctor_set(v___x_2893_, 0, v___x_2948_);
v___x_2950_ = v___x_2893_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_a_2937_);
lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_fvarId_2935_);
lean_ctor_set(v_reuseFailAlloc_2957_, 3, v_a_2941_);
v___x_2950_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2952_; 
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v___x_2950_);
v___x_2952_ = v___x_2886_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2954_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_2952_);
v___x_2954_ = v___x_2945_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec(v_a_2941_);
lean_dec(v_a_2937_);
lean_dec(v_fvarId_2935_);
lean_del_object(v___x_2893_);
lean_del_object(v___x_2886_);
v_a_2959_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2942_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2942_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v_a_2937_);
lean_dec(v_fvarId_2935_);
lean_del_object(v___x_2893_);
lean_dec(v_typeName_2888_);
lean_del_object(v___x_2886_);
v_a_2967_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2940_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2940_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec(v_fvarId_2935_);
lean_del_object(v___x_2893_);
lean_dec_ref(v_alts_2891_);
lean_dec(v_typeName_2888_);
lean_del_object(v___x_2886_);
v_a_2975_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2936_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2936_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
uint8_t v___x_2983_; lean_object* v___x_2984_; 
lean_del_object(v___x_2893_);
lean_dec_ref(v_alts_2891_);
lean_dec_ref(v_resultType_2889_);
lean_dec(v_typeName_2888_);
lean_del_object(v___x_2886_);
v___x_2983_ = 1;
v___x_2984_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2983_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
return v___x_2984_;
}
}
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_del_object(v___x_2893_);
lean_dec_ref(v_alts_2891_);
lean_dec(v_discr_2890_);
lean_dec_ref(v_resultType_2889_);
lean_dec(v_typeName_2888_);
lean_del_object(v___x_2886_);
v_a_2985_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2895_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2895_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3016_; 
v_fvarId_2995_ = lean_ctor_get(v_c_2675_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v_c_2675_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_2997_ = v_c_2675_;
v_isShared_2998_ = v_isSharedCheck_3016_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_fvarId_2995_);
lean_dec(v_c_2675_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3016_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_2999_; lean_object* v_subst_3000_; uint8_t v___x_3001_; lean_object* v___x_3002_; 
v___x_2999_ = lean_st_ref_get(v_a_2676_);
v_subst_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_ref(v_subst_3000_);
lean_dec(v___x_2999_);
v___x_3001_ = 1;
v___x_3002_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3000_, v_fvarId_2995_, v___x_3001_);
lean_dec_ref(v_subst_3000_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_fvarId_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3013_; 
v_fvarId_3003_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3005_ = v___x_3002_;
v_isShared_3006_ = v_isSharedCheck_3013_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_fvarId_3003_);
lean_dec(v___x_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3013_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v_fvarId_3003_);
v___x_3008_ = v___x_2997_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_fvarId_3003_);
v___x_3008_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3010_; 
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3008_);
v___x_3010_ = v___x_3005_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
else
{
uint8_t v___x_3014_; lean_object* v___x_3015_; 
lean_del_object(v___x_2997_);
v___x_3014_ = 1;
v___x_3015_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3014_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
return v___x_3015_;
}
}
}
default: 
{
lean_object* v_type_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3041_; 
v_type_3017_ = lean_ctor_get(v_c_2675_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_c_2675_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3019_ = v_c_2675_;
v_isShared_3020_ = v_isSharedCheck_3041_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_type_3017_);
lean_dec(v_c_2675_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3041_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3021_; 
v___x_3021_ = l_Lean_Compiler_LCNF_toImpureType(v_type_3017_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3032_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3032_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3032_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 0, v_a_3022_);
v___x_3027_ = v___x_3019_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3029_; 
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3027_);
v___x_3029_ = v___x_3024_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_del_object(v___x_3019_);
v_a_3033_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3021_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3021_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(lean_object* v_decl_3042_, lean_object* v_k_3043_, lean_object* v_ctorInfo_3044_, lean_object* v_fields_3045_, lean_object* v_irArgs_3046_, lean_object* v_i_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3054_ = lean_array_get_size(v_irArgs_3046_);
v___x_3055_ = lean_nat_dec_lt(v_i_3047_, v___x_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
lean_dec(v_i_3047_);
lean_dec_ref(v_decl_3042_);
v___x_3056_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_3043_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
return v___x_3056_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_array_fget_borrowed(v_irArgs_3046_, v_i_3047_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = lean_unsigned_to_nat(1u);
v___x_3059_ = lean_nat_add(v_i_3047_, v___x_3058_);
lean_dec(v_i_3047_);
v_i_3047_ = v___x_3059_;
goto _start;
}
else
{
lean_object* v_fvarId_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_fvarId_3061_ = lean_ctor_get(v___x_3057_, 0);
v___x_3062_ = lean_box(0);
v___x_3063_ = lean_array_get_borrowed(v___x_3062_, v_fields_3045_, v_i_3047_);
switch(lean_obj_tag(v___x_3063_))
{
case 1:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = lean_unsigned_to_nat(1u);
v___x_3065_ = lean_nat_add(v_i_3047_, v___x_3064_);
lean_dec(v_i_3047_);
v_i_3047_ = v___x_3065_;
goto _start;
}
case 2:
{
lean_object* v_i_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v_i_3067_ = lean_ctor_get(v___x_3063_, 0);
v___x_3068_ = lean_unsigned_to_nat(1u);
v___x_3069_ = lean_nat_add(v_i_3047_, v___x_3068_);
lean_dec(v_i_3047_);
lean_inc_ref(v_decl_3042_);
v___x_3070_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_3042_, v_k_3043_, v_ctorInfo_3044_, v_fields_3045_, v_irArgs_3046_, v___x_3069_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3089_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3073_ = v___x_3070_;
v_isShared_3074_ = v_isSharedCheck_3089_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3070_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3089_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v_fvarId_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3085_; 
v_fvarId_3075_ = lean_ctor_get(v_decl_3042_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_decl_3042_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; lean_object* v_unused_3087_; lean_object* v_unused_3088_; 
v_unused_3086_ = lean_ctor_get(v_decl_3042_, 3);
lean_dec(v_unused_3086_);
v_unused_3087_ = lean_ctor_get(v_decl_3042_, 2);
lean_dec(v_unused_3087_);
v_unused_3088_ = lean_ctor_get(v_decl_3042_, 1);
lean_dec(v_unused_3088_);
v___x_3077_ = v_decl_3042_;
v_isShared_3078_ = v_isSharedCheck_3085_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_fvarId_3075_);
lean_dec(v_decl_3042_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3085_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
lean_inc(v_fvarId_3061_);
lean_inc(v_i_3067_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set_tag(v___x_3077_, 8);
lean_ctor_set(v___x_3077_, 3, v_a_3071_);
lean_ctor_set(v___x_3077_, 2, v_fvarId_3061_);
lean_ctor_set(v___x_3077_, 1, v_i_3067_);
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_fvarId_3075_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_i_3067_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v_fvarId_3061_);
lean_ctor_set(v_reuseFailAlloc_3084_, 3, v_a_3071_);
v___x_3080_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3082_; 
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 0, v___x_3080_);
v___x_3082_ = v___x_3073_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_3042_);
return v___x_3070_;
}
}
case 3:
{
lean_object* v_offset_3090_; lean_object* v_type_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v_offset_3090_ = lean_ctor_get(v___x_3063_, 1);
v_type_3091_ = lean_ctor_get(v___x_3063_, 2);
v___x_3092_ = lean_unsigned_to_nat(1u);
v___x_3093_ = lean_nat_add(v_i_3047_, v___x_3092_);
lean_dec(v_i_3047_);
lean_inc_ref(v_decl_3042_);
v___x_3094_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_3042_, v_k_3043_, v_ctorInfo_3044_, v_fields_3045_, v_irArgs_3046_, v___x_3093_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3107_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3107_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3107_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v_fvarId_3099_; lean_object* v_size_3100_; lean_object* v_usize_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3105_; 
v_fvarId_3099_ = lean_ctor_get(v_decl_3042_, 0);
lean_inc(v_fvarId_3099_);
lean_dec_ref(v_decl_3042_);
v_size_3100_ = lean_ctor_get(v_ctorInfo_3044_, 2);
v_usize_3101_ = lean_ctor_get(v_ctorInfo_3044_, 3);
v___x_3102_ = lean_nat_add(v_size_3100_, v_usize_3101_);
lean_inc_ref(v_type_3091_);
lean_inc(v_fvarId_3061_);
lean_inc(v_offset_3090_);
v___x_3103_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_3103_, 0, v_fvarId_3099_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
lean_ctor_set(v___x_3103_, 2, v_offset_3090_);
lean_ctor_set(v___x_3103_, 3, v_fvarId_3061_);
lean_ctor_set(v___x_3103_, 4, v_type_3091_);
lean_ctor_set(v___x_3103_, 5, v_a_3095_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 0, v___x_3103_);
v___x_3105_ = v___x_3097_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3103_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
else
{
lean_dec_ref(v_decl_3042_);
return v___x_3094_;
}
}
default: 
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = lean_unsigned_to_nat(1u);
v___x_3109_ = lean_nat_add(v_i_3047_, v___x_3108_);
lean_dec(v_i_3047_);
v_i_3047_ = v___x_3109_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(lean_object* v_decl_3111_, lean_object* v_k_3112_, lean_object* v_ctorInfo_3113_, lean_object* v_fields_3114_, lean_object* v_irArgs_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = lean_unsigned_to_nat(0u);
v___x_3123_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_3111_, v_k_3112_, v_ctorInfo_3113_, v_fields_3114_, v_irArgs_3115_, v___x_3122_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(lean_object* v_decl_3124_, lean_object* v_k_3125_, lean_object* v_ctorInfo_3126_, lean_object* v_fields_3127_, lean_object* v_irArgs_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_3124_, v_k_3125_, v_ctorInfo_3126_, v_fields_3127_, v_irArgs_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
lean_dec(v_a_3129_);
lean_dec_ref(v_irArgs_3128_);
lean_dec_ref(v_fields_3127_);
lean_dec_ref(v_ctorInfo_3126_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(lean_object* v_decl_3136_, lean_object* v_k_3137_, lean_object* v_name_3138_, lean_object* v_args_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_3136_, v_k_3137_, v_name_3138_, v_args_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
lean_dec(v_a_3140_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(lean_object* v_decl_3147_, lean_object* v_k_3148_, lean_object* v_name_3149_, lean_object* v_args_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_3147_, v_k_3148_, v_name_3149_, v_args_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_a_3151_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object* v_decl_3158_, lean_object* v_k_3159_, lean_object* v_name_3160_, lean_object* v_numParams_3161_, lean_object* v_args_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_3158_, v_k_3159_, v_name_3160_, v_numParams_3161_, v_args_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_);
lean_dec(v_a_3167_);
lean_dec_ref(v_a_3166_);
lean_dec(v_a_3165_);
lean_dec_ref(v_a_3164_);
lean_dec(v_a_3163_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object* v_fvarId_3170_, lean_object* v_sz_3171_, lean_object* v_i_3172_, lean_object* v_bs_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
size_t v_sz_boxed_3180_; size_t v_i_boxed_3181_; lean_object* v_res_3182_; 
v_sz_boxed_3180_ = lean_unbox_usize(v_sz_3171_);
lean_dec(v_sz_3171_);
v_i_boxed_3181_ = lean_unbox_usize(v_i_3172_);
lean_dec(v_i_3172_);
v_res_3182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_3170_, v_sz_boxed_3180_, v_i_boxed_3181_, v_bs_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object* v_k_3183_, lean_object* v_decl_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_3183_, v_decl_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_3188_);
lean_dec(v_a_3187_);
lean_dec_ref(v_a_3186_);
lean_dec(v_a_3185_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object* v_discr_3192_, lean_object* v_alt_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_discr_3192_, v_alt_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object* v_decl_3201_, lean_object* v_k_3202_, lean_object* v_name_3203_, lean_object* v_numParams_3204_, lean_object* v_args_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_3201_, v_k_3202_, v_name_3203_, v_numParams_3204_, v_args_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec_ref(v_a_3207_);
lean_dec(v_a_3206_);
lean_dec_ref(v_args_3205_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* v_decl_3213_, lean_object* v_k_3214_, lean_object* v_ctorInfo_3215_, lean_object* v_fields_3216_, lean_object* v_irArgs_3217_, lean_object* v_i_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_3213_, v_k_3214_, v_ctorInfo_3215_, v_fields_3216_, v_irArgs_3217_, v_i_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_irArgs_3217_);
lean_dec_ref(v_fields_3216_);
lean_dec_ref(v_ctorInfo_3215_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object* v_k_3226_, lean_object* v_fvarId_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_3226_, v_fvarId_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_);
lean_dec(v_a_3232_);
lean_dec_ref(v_a_3231_);
lean_dec(v_a_3230_);
lean_dec_ref(v_a_3229_);
lean_dec(v_a_3228_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(lean_object* v_discr_3235_, lean_object* v_k_3236_, lean_object* v_ctorInfo_3237_, lean_object* v_params_3238_, lean_object* v_fields_3239_, lean_object* v_i_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_3235_, v_k_3236_, v_ctorInfo_3237_, v_params_3238_, v_fields_3239_, v_i_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
lean_dec(v_a_3245_);
lean_dec_ref(v_a_3244_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
lean_dec(v_a_3241_);
lean_dec_ref(v_fields_3239_);
lean_dec_ref(v_params_3238_);
lean_dec_ref(v_ctorInfo_3237_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(lean_object* v_c_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_c_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_);
lean_dec(v_a_3253_);
lean_dec_ref(v_a_3252_);
lean_dec(v_a_3251_);
lean_dec_ref(v_a_3250_);
lean_dec(v_a_3249_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(lean_object* v_decl_3256_, lean_object* v_k_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_3256_, v_k_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_);
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
lean_dec(v_a_3260_);
lean_dec_ref(v_a_3259_);
lean_dec(v_a_3258_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(lean_object* v_00_u03b1_3265_, lean_object* v_msg_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_3266_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(lean_object* v_00_u03b1_3274_, lean_object* v_msg_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(v_00_u03b1_3274_, v_msg_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(size_t v_sz_3283_, size_t v_i_3284_, lean_object* v_bs_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_3283_, v_i_3284_, v_bs_3285_, v___y_3286_, v___y_3288_, v___y_3289_, v___y_3290_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(lean_object* v_sz_3293_, lean_object* v_i_3294_, lean_object* v_bs_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
size_t v_sz_boxed_3302_; size_t v_i_boxed_3303_; lean_object* v_res_3304_; 
v_sz_boxed_3302_ = lean_unbox_usize(v_sz_3293_);
lean_dec(v_sz_3293_);
v_i_boxed_3303_ = lean_unbox_usize(v_i_3294_);
lean_dec(v_i_3294_);
v_res_3304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(v_sz_boxed_3302_, v_i_boxed_3303_, v_bs_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(lean_object* v_as_3305_, size_t v_i_3306_, size_t v_stop_3307_, lean_object* v_b_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_3305_, v_i_3306_, v_stop_3307_, v_b_3308_, v___y_3309_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(lean_object* v_as_3316_, lean_object* v_i_3317_, lean_object* v_stop_3318_, lean_object* v_b_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
size_t v_i_boxed_3326_; size_t v_stop_boxed_3327_; lean_object* v_res_3328_; 
v_i_boxed_3326_ = lean_unbox_usize(v_i_3317_);
lean_dec(v_i_3317_);
v_stop_boxed_3327_ = lean_unbox_usize(v_stop_3318_);
lean_dec(v_stop_3318_);
v_res_3328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(v_as_3316_, v_i_boxed_3326_, v_stop_boxed_3327_, v_b_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v_as_3316_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(lean_object* v_upperBound_3329_, lean_object* v_params_3330_, lean_object* v___x_3331_, lean_object* v_discr_3332_, lean_object* v_inst_3333_, lean_object* v_R_3334_, lean_object* v_a_3335_, lean_object* v_b_3336_, lean_object* v_c_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_3329_, v_params_3330_, v___x_3331_, v_discr_3332_, v_a_3335_, v_b_3336_, v___y_3338_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(lean_object* v_upperBound_3345_, lean_object* v_params_3346_, lean_object* v___x_3347_, lean_object* v_discr_3348_, lean_object* v_inst_3349_, lean_object* v_R_3350_, lean_object* v_a_3351_, lean_object* v_b_3352_, lean_object* v_c_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(v_upperBound_3345_, v_params_3346_, v___x_3347_, v_discr_3348_, v_inst_3349_, v_R_3350_, v_a_3351_, v_b_3352_, v_c_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec(v___x_3347_);
lean_dec_ref(v_params_3346_);
lean_dec(v_upperBound_3345_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(size_t v_sz_3361_, size_t v_i_3362_, lean_object* v_bs_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_3361_, v_i_3362_, v_bs_3363_, v___y_3364_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___boxed(lean_object* v_sz_3371_, lean_object* v_i_3372_, lean_object* v_bs_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
size_t v_sz_boxed_3380_; size_t v_i_boxed_3381_; lean_object* v_res_3382_; 
v_sz_boxed_3380_ = lean_unbox_usize(v_sz_3371_);
lean_dec(v_sz_3371_);
v_i_boxed_3381_ = lean_unbox_usize(v_i_3372_);
lean_dec(v_i_3372_);
v_res_3382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(v_sz_boxed_3380_, v_i_boxed_3381_, v_bs_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(lean_object* v_upperBound_3383_, lean_object* v_fieldInfo_3384_, lean_object* v___x_3385_, lean_object* v_inst_3386_, lean_object* v_R_3387_, lean_object* v_a_3388_, lean_object* v_b_3389_, lean_object* v_c_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v___x_3397_; 
v___x_3397_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_3383_, v_fieldInfo_3384_, v___x_3385_, v_a_3388_, v_b_3389_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(lean_object* v_upperBound_3398_, lean_object* v_fieldInfo_3399_, lean_object* v___x_3400_, lean_object* v_inst_3401_, lean_object* v_R_3402_, lean_object* v_a_3403_, lean_object* v_b_3404_, lean_object* v_c_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(v_upperBound_3398_, v_fieldInfo_3399_, v___x_3400_, v_inst_3401_, v_R_3402_, v_a_3403_, v_b_3404_, v_c_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___x_3400_);
lean_dec_ref(v_fieldInfo_3399_);
lean_dec(v_upperBound_3398_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(lean_object* v_00_u03b2_3413_, lean_object* v_m_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___redArg(v_m_3414_, v_a_3415_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___boxed(lean_object* v_00_u03b2_3417_, lean_object* v_m_3418_, lean_object* v_a_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_00_u03b2_3417_, v_m_3418_, v_a_3419_);
lean_dec(v_a_3419_);
lean_dec_ref(v_m_3418_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(lean_object* v_00_u03b2_3421_, lean_object* v_m_3422_, lean_object* v_query_3423_){
_start:
{
lean_object* v___x_3424_; 
v___x_3424_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___redArg(v_m_3422_, v_query_3423_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___boxed(lean_object* v_00_u03b2_3425_, lean_object* v_m_3426_, lean_object* v_query_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(v_00_u03b2_3425_, v_m_3426_, v_query_3427_);
lean_dec(v_query_3427_);
lean_dec_ref(v_m_3426_);
return v_res_3428_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0));
v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
return v___x_3431_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2));
v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
return v___x_3434_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5(void){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4));
v___x_3437_ = l_Lean_stringToMessageData(v___x_3436_);
return v___x_3437_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7(void){
_start:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6));
v___x_3440_ = l_Lean_stringToMessageData(v___x_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(lean_object* v_decl_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v_toSignature_3448_; lean_object* v_value_3449_; uint8_t v_recursive_3450_; lean_object* v_inlineAttr_x3f_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3583_; 
v_toSignature_3448_ = lean_ctor_get(v_decl_3441_, 0);
v_value_3449_ = lean_ctor_get(v_decl_3441_, 1);
v_recursive_3450_ = lean_ctor_get_uint8(v_decl_3441_, sizeof(void*)*3);
v_inlineAttr_x3f_3451_ = lean_ctor_get(v_decl_3441_, 2);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_decl_3441_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3453_ = v_decl_3441_;
v_isShared_3454_ = v_isSharedCheck_3583_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_inlineAttr_x3f_3451_);
lean_inc(v_value_3449_);
lean_inc(v_toSignature_3448_);
lean_dec(v_decl_3441_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3583_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v_name_3455_; lean_object* v_levelParams_3456_; lean_object* v_type_3457_; lean_object* v_params_3458_; uint8_t v_safe_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3582_; 
v_name_3455_ = lean_ctor_get(v_toSignature_3448_, 0);
v_levelParams_3456_ = lean_ctor_get(v_toSignature_3448_, 1);
v_type_3457_ = lean_ctor_get(v_toSignature_3448_, 2);
v_params_3458_ = lean_ctor_get(v_toSignature_3448_, 3);
v_safe_3459_ = lean_ctor_get_uint8(v_toSignature_3448_, sizeof(void*)*4);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_toSignature_3448_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3461_ = v_toSignature_3448_;
v_isShared_3462_ = v_isSharedCheck_3582_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_params_3458_);
lean_inc(v_type_3457_);
lean_inc(v_levelParams_3456_);
lean_inc(v_name_3455_);
lean_dec(v_toSignature_3448_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3582_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
size_t v_sz_3463_; size_t v___x_3464_; lean_object* v___x_3465_; 
v_sz_3463_ = lean_array_size(v_params_3458_);
v___x_3464_ = ((size_t)0ULL);
lean_inc_ref(v_params_3458_);
v___x_3465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_3463_, v___x_3464_, v_params_3458_, v_a_3442_, v_a_3444_, v_a_3445_, v_a_3446_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
v___x_3467_ = lean_array_get_size(v_params_3458_);
lean_dec_ref(v_params_3458_);
v___x_3468_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_3457_, v___x_3467_, v_a_3445_, v_a_3446_);
lean_dec_ref(v_type_3457_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3565_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3471_ = v___x_3468_;
v_isShared_3472_ = v_isSharedCheck_3565_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3468_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3565_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3473_; lean_object* v_env_3474_; lean_object* v___x_3475_; uint8_t v___x_3476_; 
v___x_3473_ = lean_st_ref_get(v_a_3446_);
v_env_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc_ref(v_env_3474_);
lean_dec(v___x_3473_);
v___x_3475_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
lean_inc(v_name_3455_);
v___x_3476_ = l_Lean_TagAttribute_hasTag(v___x_3475_, v_env_3474_, v_name_3455_);
if (lean_obj_tag(v_value_3449_) == 0)
{
lean_object* v_code_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3527_; 
lean_del_object(v___x_3471_);
v_code_3477_ = lean_ctor_get(v_value_3449_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_value_3449_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3479_ = v_value_3449_;
v_isShared_3480_ = v_isSharedCheck_3527_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_code_3477_);
lean_dec(v_value_3449_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3527_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; 
if (v___x_3476_ == 0)
{
v___y_3482_ = v_a_3442_;
v___y_3483_ = v_a_3443_;
v___y_3484_ = v_a_3444_;
v___y_3485_ = v_a_3445_;
v___y_3486_ = v_a_3446_;
goto v___jp_3481_;
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_del_object(v___x_3479_);
lean_dec_ref(v_code_3477_);
lean_dec(v_a_3469_);
lean_dec(v_a_3466_);
lean_del_object(v___x_3461_);
lean_dec(v_levelParams_3456_);
lean_del_object(v___x_3453_);
lean_dec(v_inlineAttr_x3f_3451_);
v___x_3513_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1);
v___x_3514_ = l_Lean_MessageData_ofName(v_name_3455_);
v___x_3515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3513_);
lean_ctor_set(v___x_3515_, 1, v___x_3514_);
v___x_3516_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3);
v___x_3517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3515_);
lean_ctor_set(v___x_3517_, 1, v___x_3516_);
v___x_3518_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_3517_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_);
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3518_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
v___jp_3481_:
{
lean_object* v___x_3487_; 
v___x_3487_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_3477_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3504_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3490_ = v___x_3487_;
v_isShared_3491_ = v_isSharedCheck_3504_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3487_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3504_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 3, v_a_3466_);
lean_ctor_set(v___x_3461_, 2, v_a_3469_);
v___x_3493_ = v___x_3461_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_name_3455_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_levelParams_3456_);
lean_ctor_set(v_reuseFailAlloc_3503_, 2, v_a_3469_);
lean_ctor_set(v_reuseFailAlloc_3503_, 3, v_a_3466_);
lean_ctor_set_uint8(v_reuseFailAlloc_3503_, sizeof(void*)*4, v_safe_3459_);
v___x_3493_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
lean_object* v___x_3495_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v_a_3488_);
v___x_3495_ = v___x_3479_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3488_);
v___x_3495_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
lean_object* v___x_3497_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 1, v___x_3495_);
lean_ctor_set(v___x_3453_, 0, v___x_3493_);
v___x_3497_ = v___x_3453_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3501_, 2, v_inlineAttr_x3f_3451_);
lean_ctor_set_uint8(v_reuseFailAlloc_3501_, sizeof(void*)*3, v_recursive_3450_);
v___x_3497_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3499_; 
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v___x_3497_);
v___x_3499_ = v___x_3490_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_del_object(v___x_3479_);
lean_dec(v_a_3469_);
lean_dec(v_a_3466_);
lean_del_object(v___x_3461_);
lean_dec(v_levelParams_3456_);
lean_dec(v_name_3455_);
lean_del_object(v___x_3453_);
lean_dec(v_inlineAttr_x3f_3451_);
v_a_3505_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3487_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3487_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
}
else
{
lean_object* v_externAttrData_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3564_; 
v_externAttrData_3528_ = lean_ctor_get(v_value_3449_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_value_3449_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3530_ = v_value_3449_;
v_isShared_3531_ = v_isSharedCheck_3564_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_externAttrData_3528_);
lean_dec(v_value_3449_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3564_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v_resultType_3533_; 
if (v___x_3476_ == 0)
{
v_resultType_3533_ = v_a_3469_;
goto v___jp_3532_;
}
else
{
uint8_t v___x_3546_; 
v___x_3546_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_3469_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; 
lean_dec(v_a_3469_);
v___x_3547_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
v_resultType_3533_ = v___x_3547_;
goto v___jp_3532_;
}
else
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_del_object(v___x_3530_);
lean_dec(v_externAttrData_3528_);
lean_del_object(v___x_3471_);
lean_dec(v_a_3466_);
lean_del_object(v___x_3461_);
lean_dec(v_levelParams_3456_);
lean_del_object(v___x_3453_);
lean_dec(v_inlineAttr_x3f_3451_);
v___x_3548_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5);
v___x_3549_ = l_Lean_MessageData_ofName(v_name_3455_);
v___x_3550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3548_);
lean_ctor_set(v___x_3550_, 1, v___x_3549_);
v___x_3551_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7);
v___x_3552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3550_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = l_Lean_MessageData_ofExpr(v_a_3469_);
v___x_3554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3552_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
v___x_3555_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_3554_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_);
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
v___jp_3532_:
{
lean_object* v___x_3535_; 
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 3, v_a_3466_);
lean_ctor_set(v___x_3461_, 2, v_resultType_3533_);
v___x_3535_ = v___x_3461_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_name_3455_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v_levelParams_3456_);
lean_ctor_set(v_reuseFailAlloc_3545_, 2, v_resultType_3533_);
lean_ctor_set(v_reuseFailAlloc_3545_, 3, v_a_3466_);
lean_ctor_set_uint8(v_reuseFailAlloc_3545_, sizeof(void*)*4, v_safe_3459_);
v___x_3535_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
lean_object* v___x_3537_; 
if (v_isShared_3531_ == 0)
{
v___x_3537_ = v___x_3530_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_externAttrData_3528_);
v___x_3537_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
lean_object* v___x_3539_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 1, v___x_3537_);
lean_ctor_set(v___x_3453_, 0, v___x_3535_);
v___x_3539_ = v___x_3453_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3535_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v___x_3537_);
lean_ctor_set(v_reuseFailAlloc_3543_, 2, v_inlineAttr_x3f_3451_);
lean_ctor_set_uint8(v_reuseFailAlloc_3543_, sizeof(void*)*3, v_recursive_3450_);
v___x_3539_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3541_; 
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3539_);
v___x_3541_ = v___x_3471_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
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
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_dec(v_a_3466_);
lean_del_object(v___x_3461_);
lean_dec(v_levelParams_3456_);
lean_dec(v_name_3455_);
lean_del_object(v___x_3453_);
lean_dec(v_inlineAttr_x3f_3451_);
lean_dec_ref(v_value_3449_);
v_a_3566_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3468_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3468_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_del_object(v___x_3461_);
lean_dec_ref(v_params_3458_);
lean_dec_ref(v_type_3457_);
lean_dec(v_levelParams_3456_);
lean_dec(v_name_3455_);
lean_del_object(v___x_3453_);
lean_dec(v_inlineAttr_x3f_3451_);
lean_dec_ref(v_value_3449_);
v_a_3574_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3465_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3465_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___boxed(lean_object* v_decl_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_);
lean_dec(v_a_3589_);
lean_dec_ref(v_a_3588_);
lean_dec(v_a_3587_);
lean_dec_ref(v_a_3586_);
lean_dec(v_a_3585_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(lean_object* v_decl_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v___x_3599_; 
v___x_3599_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3601_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc_n(v_a_3600_, 2);
lean_dec_ref_known(v___x_3599_, 1);
v___x_3601_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_3600_, v_a_3597_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3608_ == 0)
{
lean_object* v_unused_3609_; 
v_unused_3609_ = lean_ctor_get(v___x_3601_, 0);
lean_dec(v_unused_3609_);
v___x_3603_ = v___x_3601_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_dec(v___x_3601_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v_a_3600_);
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3600_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec(v_a_3600_);
v_a_3610_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3601_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3601_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
return v___x_3599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go___boxed(lean_object* v_decl_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
lean_dec(v_a_3623_);
lean_dec_ref(v_a_3622_);
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3620_);
lean_dec(v_a_3619_);
return v_res_3625_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0(void){
_start:
{
lean_object* v_cellCount_3626_; lean_object* v___x_3627_; 
v_cellCount_3626_ = lean_unsigned_to_nat(16u);
v___x_3627_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3626_);
return v___x_3627_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1(void){
_start:
{
lean_object* v_cellCount_3628_; lean_object* v___x_3629_; 
v_cellCount_3628_ = lean_unsigned_to_nat(16u);
v___x_3629_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3628_);
return v___x_3629_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2(void){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3630_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1);
v___x_3631_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0);
v___x_3632_ = lean_unsigned_to_nat(0u);
v___x_3633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
lean_ctor_set(v___x_3633_, 1, v___x_3631_);
lean_ctor_set(v___x_3633_, 2, v___x_3630_);
return v___x_3633_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__3(void){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2);
v___x_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(lean_object* v_decl_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3642_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__3);
v___x_3643_ = lean_st_mk_ref(v___x_3642_);
v___x_3644_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_3636_, v___x_3643_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3653_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3647_ = v___x_3644_;
v_isShared_3648_ = v_isSharedCheck_3653_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3644_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3653_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3649_; lean_object* v___x_3651_; 
v___x_3649_ = lean_st_ref_get(v___x_3643_);
lean_dec(v___x_3643_);
lean_dec(v___x_3649_);
if (v_isShared_3648_ == 0)
{
v___x_3651_ = v___x_3647_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3645_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
else
{
lean_dec(v___x_3643_);
return v___x_3644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___boxed(lean_object* v_decl_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_decl_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
lean_dec(v_a_3658_);
lean_dec_ref(v_a_3657_);
lean_dec(v_a_3656_);
lean_dec_ref(v_a_3655_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(size_t v_sz_3661_, size_t v_i_3662_, lean_object* v_bs_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
uint8_t v___x_3669_; 
v___x_3669_ = lean_usize_dec_lt(v_i_3662_, v_sz_3661_);
if (v___x_3669_ == 0)
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3670_, 0, v_bs_3663_);
return v___x_3670_;
}
else
{
lean_object* v_v_3671_; lean_object* v___x_3672_; 
v_v_3671_ = lean_array_uget_borrowed(v_bs_3663_, v_i_3662_);
lean_inc(v_v_3671_);
v___x_3672_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_v_3671_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3674_; lean_object* v_bs_x27_3675_; size_t v___x_3676_; size_t v___x_3677_; lean_object* v___x_3678_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_a_3673_);
lean_dec_ref_known(v___x_3672_, 1);
v___x_3674_ = lean_unsigned_to_nat(0u);
v_bs_x27_3675_ = lean_array_uset(v_bs_3663_, v_i_3662_, v___x_3674_);
v___x_3676_ = ((size_t)1ULL);
v___x_3677_ = lean_usize_add(v_i_3662_, v___x_3676_);
v___x_3678_ = lean_array_uset(v_bs_x27_3675_, v_i_3662_, v_a_3673_);
v_i_3662_ = v___x_3677_;
v_bs_3663_ = v___x_3678_;
goto _start;
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_dec_ref(v_bs_3663_);
v_a_3680_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3672_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3672_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0___boxed(lean_object* v_sz_3688_, lean_object* v_i_3689_, lean_object* v_bs_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
size_t v_sz_boxed_3696_; size_t v_i_boxed_3697_; lean_object* v_res_3698_; 
v_sz_boxed_3696_ = lean_unbox_usize(v_sz_3688_);
lean_dec(v_sz_3688_);
v_i_boxed_3697_ = lean_unbox_usize(v_i_3689_);
lean_dec(v_i_3689_);
v_res_3698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_boxed_3696_, v_i_boxed_3697_, v_bs_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0(lean_object* v_x_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
size_t v_sz_3705_; size_t v___x_3706_; lean_object* v___x_3707_; 
v_sz_3705_ = lean_array_size(v_x_3699_);
v___x_3706_ = ((size_t)0ULL);
v___x_3707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_3705_, v___x_3706_, v_x_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0___boxed(lean_object* v_x_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Lean_Compiler_LCNF_toImpure___lam__0(v_x_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3765_; uint8_t v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3765_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3766_ = 1;
v___x_3767_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3768_ = l_Lean_registerTraceClass(v___x_3765_, v___x_3766_, v___x_3767_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2____boxed(lean_object* v_a_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
return v_res_3770_;
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
