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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t, lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
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
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_getCtorLayout(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CtorInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v_res_7_;
v_res_7_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(v_x_1_, v___y_2_, v___y_3_);
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object* v_x_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(v_x_8_, v___y_9_, v___y_10_);
lean_dec(v___y_10_);
lean_dec_ref(v___y_9_);
lean_dec(v_x_8_);
return v_res_12_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; lean_object* v___x_62_; 
v___f_55_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_56_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_57_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_58_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_59_ = 0;
v___x_60_ = lean_box(2);
v___x_61_ = 0;
v___x_62_ = l_Lean_registerTagAttribute(v___x_56_, v___x_57_, v___f_55_, v___x_58_, v___x_59_, v___x_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_63_;
v_res_63_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
return v_res_65_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1(){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_69_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0));
v___x_70_ = l_Lean_addBuiltinDocString(v___x_68_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_71_;
v_res_71_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___boxed(lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
return v_res_73_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3(){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_101_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6));
v___x_102_ = l_Lean_addBuiltinDeclarationRanges(v___x_100_, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_103_;
v_res_103_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3();
stack->m_obj
 = v_res_103_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___boxed(lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3();
return v_res_105_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(lean_object* v_____do__lift_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_subst_113_; lean_object* v___x_114_; 
v_subst_113_ = lean_ctor_get(v_____do__lift_106_, 0);
lean_inc_ref(v_subst_113_);
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v_subst_113_);
return v___x_114_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_106_ = stack[0].m_obj;
lean_object* v___y_107_ = stack[1].m_obj;
lean_object* v___y_108_ = stack[2].m_obj;
lean_object* v___y_109_ = stack[3].m_obj;
lean_object* v___y_110_ = stack[4].m_obj;
lean_object* v___y_111_ = stack[5].m_obj;
lean_object* v_res_115_;
v_res_115_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(v_____do__lift_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
stack->m_obj
 = v_res_115_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed(lean_object* v_____do__lift_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(v_____do__lift_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v_____do__lift_116_);
return v_res_123_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_instMonadEIO___redArg();
return v___x_124_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0);
v___x_126_ = l_StateRefT_x27_instMonad___redArg(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue(void){
_start:
{
lean_object* v___x_155_; lean_object* v_toApplicative_156_; lean_object* v_toFunctor_157_; lean_object* v_toSeq_158_; lean_object* v_toSeqLeft_159_; lean_object* v_toSeqRight_160_; lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_toApplicative_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_202_; 
v___x_155_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_156_ = lean_ctor_get(v___x_155_, 0);
v_toFunctor_157_ = lean_ctor_get(v_toApplicative_156_, 0);
v_toSeq_158_ = lean_ctor_get(v_toApplicative_156_, 2);
v_toSeqLeft_159_ = lean_ctor_get(v_toApplicative_156_, 3);
v_toSeqRight_160_ = lean_ctor_get(v_toApplicative_156_, 4);
v___f_161_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_162_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref_n(v_toFunctor_157_, 2);
v___f_163_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_163_, 0, v_toFunctor_157_);
v___f_164_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_164_, 0, v_toFunctor_157_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___f_163_);
lean_ctor_set(v___x_165_, 1, v___f_164_);
lean_inc(v_toSeqRight_160_);
v___f_166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_166_, 0, v_toSeqRight_160_);
lean_inc(v_toSeqLeft_159_);
v___f_167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_167_, 0, v_toSeqLeft_159_);
lean_inc(v_toSeq_158_);
v___f_168_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_168_, 0, v_toSeq_158_);
v___x_169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_169_, 0, v___x_165_);
lean_ctor_set(v___x_169_, 1, v___f_161_);
lean_ctor_set(v___x_169_, 2, v___f_168_);
lean_ctor_set(v___x_169_, 3, v___f_167_);
lean_ctor_set(v___x_169_, 4, v___f_166_);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___f_162_);
v___x_171_ = l_StateRefT_x27_instMonad___redArg(v___x_170_);
v_toApplicative_172_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v___x_171_, 1);
lean_dec(v_unused_203_);
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_202_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_toApplicative_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_202_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v_toFunctor_176_; lean_object* v_toSeq_177_; lean_object* v_toSeqLeft_178_; lean_object* v_toSeqRight_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_200_; 
v_toFunctor_176_ = lean_ctor_get(v_toApplicative_172_, 0);
v_toSeq_177_ = lean_ctor_get(v_toApplicative_172_, 2);
v_toSeqLeft_178_ = lean_ctor_get(v_toApplicative_172_, 3);
v_toSeqRight_179_ = lean_ctor_get(v_toApplicative_172_, 4);
v_isSharedCheck_200_ = !lean_is_exclusive(v_toApplicative_172_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v_toApplicative_172_, 1);
lean_dec(v_unused_201_);
v___x_181_ = v_toApplicative_172_;
v_isShared_182_ = v_isSharedCheck_200_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_toSeqRight_179_);
lean_inc(v_toSeqLeft_178_);
lean_inc(v_toSeq_177_);
lean_inc(v_toFunctor_176_);
lean_dec(v_toApplicative_172_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_200_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___f_187_; lean_object* v___x_188_; lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___x_193_; 
v___f_183_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4));
v___f_184_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_185_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_176_);
v___f_186_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_186_, 0, v_toFunctor_176_);
v___f_187_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_187_, 0, v_toFunctor_176_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___f_186_);
lean_ctor_set(v___x_188_, 1, v___f_187_);
v___f_189_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_189_, 0, v_toSeqRight_179_);
v___f_190_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_190_, 0, v_toSeqLeft_178_);
v___f_191_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_191_, 0, v_toSeq_177_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 4, v___f_189_);
lean_ctor_set(v___x_181_, 3, v___f_190_);
lean_ctor_set(v___x_181_, 2, v___f_191_);
lean_ctor_set(v___x_181_, 1, v___f_184_);
lean_ctor_set(v___x_181_, 0, v___x_188_);
v___x_193_ = v___x_181_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___f_184_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v___f_191_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v___f_190_);
lean_ctor_set(v_reuseFailAlloc_199_, 4, v___f_189_);
v___x_193_ = v_reuseFailAlloc_199_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___f_185_);
lean_ctor_set(v___x_174_, 0, v___x_193_);
v___x_195_ = v___x_174_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___f_185_);
v___x_195_ = v_reuseFailAlloc_198_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18));
v___x_197_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_197_, 0, lean_box(0));
lean_closure_set(v___x_197_, 1, lean_box(0));
lean_closure_set(v___x_197_, 2, v___x_195_);
lean_closure_set(v___x_197_, 3, lean_box(0));
lean_closure_set(v___x_197_, 4, lean_box(0));
lean_closure_set(v___x_197_, 5, v___x_196_);
lean_closure_set(v___x_197_, 6, v___f_183_);
return v___x_197_;
}
}
}
}
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(lean_object* v_f_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; lean_object* v_subst_212_; lean_object* v_jpParamMask_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_224_; 
v___x_211_ = lean_st_ref_take(v___y_205_);
v_subst_212_ = lean_ctor_get(v___x_211_, 0);
v_jpParamMask_213_ = lean_ctor_get(v___x_211_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_224_ == 0)
{
v___x_215_ = v___x_211_;
v_isShared_216_ = v_isSharedCheck_224_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_jpParamMask_213_);
lean_inc(v_subst_212_);
lean_dec(v___x_211_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_224_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_217_ = lean_box(0);
v___x_218_ = lean_apply_1(v_f_204_, v_subst_212_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_218_);
v___x_220_ = v___x_215_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_jpParamMask_213_);
v___x_220_ = v_reuseFailAlloc_223_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_st_ref_put(v___y_205_, v___x_220_);
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_217_);
return v___x_222_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_204_ = stack[0].m_obj;
lean_object* v___y_205_ = stack[1].m_obj;
lean_object* v___y_206_ = stack[2].m_obj;
lean_object* v___y_207_ = stack[3].m_obj;
lean_object* v___y_208_ = stack[4].m_obj;
lean_object* v___y_209_ = stack[5].m_obj;
lean_object* v_res_225_;
v_res_225_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(v_f_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed(lean_object* v_f_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(v_f_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(lean_object* v_a_236_, lean_object* v_b_237_, lean_object* v_x_238_){
_start:
{
if (lean_obj_tag(v_x_238_) == 0)
{
lean_dec(v_b_237_);
lean_dec(v_a_236_);
return v_x_238_;
}
else
{
lean_object* v_key_239_; lean_object* v_value_240_; lean_object* v_tail_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_253_; 
v_key_239_ = lean_ctor_get(v_x_238_, 0);
v_value_240_ = lean_ctor_get(v_x_238_, 1);
v_tail_241_ = lean_ctor_get(v_x_238_, 2);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_238_);
if (v_isSharedCheck_253_ == 0)
{
v___x_243_ = v_x_238_;
v_isShared_244_ = v_isSharedCheck_253_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_tail_241_);
lean_inc(v_value_240_);
lean_inc(v_key_239_);
lean_dec(v_x_238_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_253_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
uint8_t v___x_245_; 
v___x_245_ = l_Lean_instBEqFVarId_beq(v_key_239_, v_a_236_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_236_, v_b_237_, v_tail_241_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 2, v___x_246_);
v___x_248_ = v___x_243_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_key_239_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_value_240_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
else
{
lean_object* v___x_251_; 
lean_dec(v_value_240_);
lean_dec(v_key_239_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v_b_237_);
lean_ctor_set(v___x_243_, 0, v_a_236_);
v___x_251_ = v___x_243_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_236_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_b_237_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_tail_241_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
return v_x_254_;
}
else
{
lean_object* v_key_256_; lean_object* v_value_257_; lean_object* v_tail_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_281_; 
v_key_256_ = lean_ctor_get(v_x_255_, 0);
v_value_257_ = lean_ctor_get(v_x_255_, 1);
v_tail_258_ = lean_ctor_get(v_x_255_, 2);
v_isSharedCheck_281_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_281_ == 0)
{
v___x_260_ = v_x_255_;
v_isShared_261_ = v_isSharedCheck_281_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_tail_258_);
lean_inc(v_value_257_);
lean_inc(v_key_256_);
lean_dec(v_x_255_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_281_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; uint64_t v___x_263_; uint64_t v___x_264_; uint64_t v___x_265_; uint64_t v_fold_266_; uint64_t v___x_267_; uint64_t v___x_268_; uint64_t v___x_269_; size_t v___x_270_; size_t v___x_271_; size_t v___x_272_; size_t v___x_273_; size_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_262_ = lean_array_get_size(v_x_254_);
v___x_263_ = l_Lean_instHashableFVarId_hash(v_key_256_);
v___x_264_ = 32ULL;
v___x_265_ = lean_uint64_shift_right(v___x_263_, v___x_264_);
v_fold_266_ = lean_uint64_xor(v___x_263_, v___x_265_);
v___x_267_ = 16ULL;
v___x_268_ = lean_uint64_shift_right(v_fold_266_, v___x_267_);
v___x_269_ = lean_uint64_xor(v_fold_266_, v___x_268_);
v___x_270_ = lean_uint64_to_usize(v___x_269_);
v___x_271_ = lean_usize_of_nat(v___x_262_);
v___x_272_ = ((size_t)1ULL);
v___x_273_ = lean_usize_sub(v___x_271_, v___x_272_);
v___x_274_ = lean_usize_land(v___x_270_, v___x_273_);
v___x_275_ = lean_array_uget_borrowed(v_x_254_, v___x_274_);
lean_inc(v___x_275_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 2, v___x_275_);
v___x_277_ = v___x_260_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_key_256_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_value_257_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v___x_275_);
v___x_277_ = v_reuseFailAlloc_280_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_278_; 
v___x_278_ = lean_array_uset(v_x_254_, v___x_274_, v___x_277_);
v_x_254_ = v___x_278_;
v_x_255_ = v_tail_258_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(lean_object* v_i_282_, lean_object* v_source_283_, lean_object* v_target_284_){
_start:
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_array_get_size(v_source_283_);
v___x_286_ = lean_nat_dec_lt(v_i_282_, v___x_285_);
if (v___x_286_ == 0)
{
lean_dec_ref(v_source_283_);
lean_dec(v_i_282_);
return v_target_284_;
}
else
{
lean_object* v_es_287_; lean_object* v___x_288_; lean_object* v_source_289_; lean_object* v_target_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_es_287_ = lean_array_fget(v_source_283_, v_i_282_);
v___x_288_ = lean_box(0);
v_source_289_ = lean_array_fset(v_source_283_, v_i_282_, v___x_288_);
v_target_290_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_target_284_, v_es_287_);
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_i_282_, v___x_291_);
lean_dec(v_i_282_);
v_i_282_ = v___x_292_;
v_source_283_ = v_source_289_;
v_target_284_ = v_target_290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(lean_object* v_data_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v_nbuckets_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_295_ = lean_array_get_size(v_data_294_);
v___x_296_ = lean_unsigned_to_nat(2u);
v_nbuckets_297_ = lean_nat_mul(v___x_295_, v___x_296_);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_box(0);
v___x_300_ = lean_mk_array(v_nbuckets_297_, v___x_299_);
v___x_301_ = lean_array_propagate_mark(v_data_294_, v___x_300_);
v___x_302_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v___x_298_, v_data_294_, v___x_301_);
return v___x_302_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(lean_object* v_a_303_, lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
uint8_t v___x_305_; 
v___x_305_ = 0;
return v___x_305_;
}
else
{
lean_object* v_key_306_; lean_object* v_tail_307_; uint8_t v___x_308_; 
v_key_306_ = lean_ctor_get(v_x_304_, 0);
v_tail_307_ = lean_ctor_get(v_x_304_, 2);
v___x_308_ = l_Lean_instBEqFVarId_beq(v_key_306_, v_a_303_);
if (v___x_308_ == 0)
{
v_x_304_ = v_tail_307_;
goto _start;
}
else
{
return v___x_308_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_303_ = stack[0].m_obj;
lean_object* v_x_304_ = stack[1].m_obj;
uint8_t v_res_310_;
v_res_310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_303_, v_x_304_);
stack->m_num = v_res_310_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg___boxed(lean_object* v_a_311_, lean_object* v_x_312_){
_start:
{
uint8_t v_res_313_; lean_object* v_r_314_; 
v_res_313_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_311_, v_x_312_);
lean_dec(v_x_312_);
lean_dec(v_a_311_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(lean_object* v_m_315_, lean_object* v_a_316_, lean_object* v_b_317_){
_start:
{
lean_object* v_size_318_; lean_object* v_buckets_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_362_; 
v_size_318_ = lean_ctor_get(v_m_315_, 0);
v_buckets_319_ = lean_ctor_get(v_m_315_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_m_315_);
if (v_isSharedCheck_362_ == 0)
{
v___x_321_ = v_m_315_;
v_isShared_322_ = v_isSharedCheck_362_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_buckets_319_);
lean_inc(v_size_318_);
lean_dec(v_m_315_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_362_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; uint64_t v___x_324_; uint64_t v___x_325_; uint64_t v___x_326_; uint64_t v_fold_327_; uint64_t v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; size_t v___x_334_; size_t v___x_335_; lean_object* v_bkt_336_; uint8_t v___x_337_; 
v___x_323_ = lean_array_get_size(v_buckets_319_);
v___x_324_ = l_Lean_instHashableFVarId_hash(v_a_316_);
v___x_325_ = 32ULL;
v___x_326_ = lean_uint64_shift_right(v___x_324_, v___x_325_);
v_fold_327_ = lean_uint64_xor(v___x_324_, v___x_326_);
v___x_328_ = 16ULL;
v___x_329_ = lean_uint64_shift_right(v_fold_327_, v___x_328_);
v___x_330_ = lean_uint64_xor(v_fold_327_, v___x_329_);
v___x_331_ = lean_uint64_to_usize(v___x_330_);
v___x_332_ = lean_usize_of_nat(v___x_323_);
v___x_333_ = ((size_t)1ULL);
v___x_334_ = lean_usize_sub(v___x_332_, v___x_333_);
v___x_335_ = lean_usize_land(v___x_331_, v___x_334_);
v_bkt_336_ = lean_array_uget_borrowed(v_buckets_319_, v___x_335_);
v___x_337_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_316_, v_bkt_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v_size_x27_339_; lean_object* v___x_340_; lean_object* v_buckets_x27_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_338_ = lean_unsigned_to_nat(1u);
v_size_x27_339_ = lean_nat_add(v_size_318_, v___x_338_);
lean_dec(v_size_318_);
lean_inc(v_bkt_336_);
v___x_340_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_340_, 0, v_a_316_);
lean_ctor_set(v___x_340_, 1, v_b_317_);
lean_ctor_set(v___x_340_, 2, v_bkt_336_);
v_buckets_x27_341_ = lean_array_uset(v_buckets_319_, v___x_335_, v___x_340_);
v___x_342_ = lean_unsigned_to_nat(4u);
v___x_343_ = lean_nat_mul(v_size_x27_339_, v___x_342_);
v___x_344_ = lean_unsigned_to_nat(3u);
v___x_345_ = lean_nat_div(v___x_343_, v___x_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_array_get_size(v_buckets_x27_341_);
v___x_347_ = lean_nat_dec_le(v___x_345_, v___x_346_);
lean_dec(v___x_345_);
if (v___x_347_ == 0)
{
lean_object* v_val_348_; lean_object* v___x_350_; 
v_val_348_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_buckets_x27_341_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 1, v_val_348_);
lean_ctor_set(v___x_321_, 0, v_size_x27_339_);
v___x_350_ = v___x_321_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_size_x27_339_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_val_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
else
{
lean_object* v___x_353_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 1, v_buckets_x27_341_);
lean_ctor_set(v___x_321_, 0, v_size_x27_339_);
v___x_353_ = v___x_321_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_size_x27_339_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_buckets_x27_341_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
else
{
lean_object* v___x_355_; lean_object* v_buckets_x27_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
lean_inc(v_bkt_336_);
v___x_355_ = lean_box(0);
v_buckets_x27_356_ = lean_array_uset(v_buckets_319_, v___x_335_, v___x_355_);
v___x_357_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_316_, v_b_317_, v_bkt_336_);
v___x_358_ = lean_array_uset(v_buckets_x27_356_, v___x_335_, v___x_357_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 1, v___x_358_);
v___x_360_ = v___x_321_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_size_318_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(lean_object* v_p_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_fvarId_369_; lean_object* v_binderName_370_; lean_object* v_type_371_; uint8_t v_borrow_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_428_; 
v_fvarId_369_ = lean_ctor_get(v_p_363_, 0);
v_binderName_370_ = lean_ctor_get(v_p_363_, 1);
v_type_371_ = lean_ctor_get(v_p_363_, 2);
v_borrow_372_ = lean_ctor_get_uint8(v_p_363_, sizeof(void*)*3);
v_isSharedCheck_428_ = !lean_is_exclusive(v_p_363_);
if (v_isSharedCheck_428_ == 0)
{
v___x_374_ = v_p_363_;
v_isShared_375_ = v_isSharedCheck_428_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_type_371_);
lean_inc(v_binderName_370_);
lean_inc(v_fvarId_369_);
lean_dec(v_p_363_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_428_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Compiler_LCNF_toImpureType(v_type_371_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_419_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_419_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_419_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_419_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___y_382_; uint8_t v___y_403_; uint8_t v___x_417_; 
v___x_417_ = l_Lean_Expr_isVoid(v_a_377_);
if (v___x_417_ == 0)
{
uint8_t v___x_418_; 
v___x_418_ = l_Lean_Expr_isErased(v_a_377_);
v___y_403_ = v___x_418_;
goto v___jp_402_;
}
else
{
v___y_403_ = v___x_417_;
goto v___jp_402_;
}
v___jp_381_:
{
uint8_t v___x_383_; lean_object* v___x_385_; 
v___x_383_ = 1;
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 2, v_a_377_);
v___x_385_ = v___x_374_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_fvarId_369_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_binderName_370_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_a_377_);
lean_ctor_set_uint8(v_reuseFailAlloc_401_, sizeof(void*)*3, v_borrow_372_);
v___x_385_ = v_reuseFailAlloc_401_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; lean_object* v_lctx_387_; lean_object* v_nextIdx_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_400_; 
v___x_386_ = lean_st_ref_take(v___y_382_);
v_lctx_387_ = lean_ctor_get(v___x_386_, 0);
v_nextIdx_388_ = lean_ctor_get(v___x_386_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_400_ == 0)
{
v___x_390_ = v___x_386_;
v_isShared_391_ = v_isSharedCheck_400_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_nextIdx_388_);
lean_inc(v_lctx_387_);
lean_dec(v___x_386_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_400_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
lean_inc_ref(v___x_385_);
v___x_392_ = l_Lean_Compiler_LCNF_LCtx_addParam(v___x_383_, v_lctx_387_, v___x_385_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_nextIdx_388_);
v___x_394_ = v_reuseFailAlloc_399_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_st_ref_put(v___y_382_, v___x_394_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_385_);
v___x_397_ = v___x_379_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_385_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
v___jp_402_:
{
if (v___y_403_ == 0)
{
v___y_382_ = v_a_365_;
goto v___jp_381_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v_subst_406_; lean_object* v_jpParamMask_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_416_; 
v___x_404_ = lean_box(0);
v___x_405_ = lean_st_ref_take(v_a_364_);
v_subst_406_ = lean_ctor_get(v___x_405_, 0);
v_jpParamMask_407_ = lean_ctor_get(v___x_405_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_416_ == 0)
{
v___x_409_ = v___x_405_;
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_jpParamMask_407_);
lean_inc(v_subst_406_);
lean_dec(v___x_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
lean_inc(v_fvarId_369_);
v___x_411_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_406_, v_fvarId_369_, v___x_404_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_jpParamMask_407_);
v___x_413_ = v_reuseFailAlloc_415_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; 
v___x_414_ = lean_st_ref_put(v_a_364_, v___x_413_);
v___y_382_ = v_a_365_;
goto v___jp_381_;
}
}
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_del_object(v___x_374_);
lean_dec(v_binderName_370_);
lean_dec(v_fvarId_369_);
v_a_420_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_376_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_376_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_363_ = stack[0].m_obj;
lean_object* v_a_364_ = stack[1].m_obj;
lean_object* v_a_365_ = stack[2].m_obj;
lean_object* v_a_366_ = stack[3].m_obj;
lean_object* v_a_367_ = stack[4].m_obj;
lean_object* v_res_429_;
v_res_429_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
stack->m_obj
 = v_res_429_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg___boxed(lean_object* v_p_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec(v_a_431_);
return v_res_436_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(lean_object* v_p_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_437_, v_a_438_, v_a_440_, v_a_441_, v_a_442_);
return v___x_444_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_437_ = stack[0].m_obj;
lean_object* v_a_438_ = stack[1].m_obj;
lean_object* v_a_439_ = stack[2].m_obj;
lean_object* v_a_440_ = stack[3].m_obj;
lean_object* v_a_441_ = stack[4].m_obj;
lean_object* v_a_442_ = stack[5].m_obj;
lean_object* v_res_445_;
v_res_445_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(v_p_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___boxed(lean_object* v_p_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(v_p_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(lean_object* v_00_u03b2_454_, lean_object* v_m_455_, lean_object* v_a_456_, lean_object* v_b_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_m_455_, v_a_456_, v_b_457_);
return v___x_458_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(lean_object* v_00_u03b2_459_, lean_object* v_a_460_, lean_object* v_x_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_460_, v_x_461_);
return v___x_462_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_460_ = stack[1].m_obj;
lean_object* v_x_461_ = stack[2].m_obj;
uint8_t v_res_463_;
v_res_463_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(lean_box(0), v_a_460_, v_x_461_);
stack->m_num = v_res_463_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___boxed(lean_object* v_00_u03b2_464_, lean_object* v_a_465_, lean_object* v_x_466_){
_start:
{
uint8_t v_res_467_; lean_object* v_r_468_; 
v_res_467_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(v_00_u03b2_464_, v_a_465_, v_x_466_);
lean_dec(v_x_466_);
lean_dec(v_a_465_);
v_r_468_ = lean_box(v_res_467_);
return v_r_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1(lean_object* v_00_u03b2_469_, lean_object* v_data_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_data_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2(lean_object* v_00_u03b2_472_, lean_object* v_a_473_, lean_object* v_b_474_, lean_object* v_x_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_473_, v_b_474_, v_x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_477_, lean_object* v_i_478_, lean_object* v_source_479_, lean_object* v_target_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v_i_478_, v_source_479_, v_target_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_482_, lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_x_483_, v_x_484_);
return v___x_485_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_box(0);
v___x_490_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_491_ = l_Lean_Expr_const___override(v___x_490_, v___x_489_);
return v___x_491_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2);
v___x_493_ = lean_box(1);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
return v___x_494_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = lean_box(0);
v___x_499_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5));
v___x_500_ = l_Lean_Expr_const___override(v___x_499_, v___x_498_);
return v___x_500_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_box(0);
v___x_505_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8));
v___x_506_ = l_Lean_Expr_const___override(v___x_505_, v___x_504_);
return v___x_506_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9);
v___x_508_ = lean_box(1);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___x_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(lean_object* v_base_510_, lean_object* v_ctorInfo_511_, lean_object* v_field_512_){
_start:
{
switch(lean_obj_tag(v_field_512_))
{
case 0:
{
lean_object* v___x_513_; 
lean_dec(v_base_510_);
v___x_513_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3);
return v___x_513_;
}
case 1:
{
lean_object* v_i_514_; lean_object* v_type_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_i_514_ = lean_ctor_get(v_field_512_, 0);
v_type_515_ = lean_ctor_get(v_field_512_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_field_512_);
if (v_isSharedCheck_523_ == 0)
{
v___x_517_ = v_field_512_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_type_515_);
lean_inc(v_i_514_);
lean_dec(v_field_512_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 6);
lean_ctor_set(v___x_517_, 1, v_base_510_);
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_i_514_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_base_510_);
v___x_520_ = v_reuseFailAlloc_522_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; 
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v_type_515_);
return v___x_521_;
}
}
}
case 2:
{
lean_object* v_i_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_i_524_ = lean_ctor_get(v_field_512_, 0);
lean_inc(v_i_524_);
lean_dec_ref_known(v_field_512_, 1);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v_i_524_);
lean_ctor_set(v___x_525_, 1, v_base_510_);
v___x_526_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
return v___x_527_;
}
case 3:
{
lean_object* v_offset_528_; lean_object* v_type_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_540_; 
v_offset_528_ = lean_ctor_get(v_field_512_, 1);
v_type_529_ = lean_ctor_get(v_field_512_, 2);
v_isSharedCheck_540_ = !lean_is_exclusive(v_field_512_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; 
v_unused_541_ = lean_ctor_get(v_field_512_, 0);
lean_dec(v_unused_541_);
v___x_531_ = v_field_512_;
v_isShared_532_ = v_isSharedCheck_540_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_type_529_);
lean_inc(v_offset_528_);
lean_dec(v_field_512_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_540_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_size_533_; lean_object* v_usize_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v_size_533_ = lean_ctor_get(v_ctorInfo_511_, 2);
v_usize_534_ = lean_ctor_get(v_ctorInfo_511_, 3);
v___x_535_ = lean_nat_add(v_size_533_, v_usize_534_);
if (v_isShared_532_ == 0)
{
lean_ctor_set_tag(v___x_531_, 8);
lean_ctor_set(v___x_531_, 2, v_base_510_);
lean_ctor_set(v___x_531_, 0, v___x_535_);
v___x_537_ = v___x_531_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_offset_528_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_base_510_);
v___x_537_ = v_reuseFailAlloc_539_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; 
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v_type_529_);
return v___x_538_;
}
}
}
default: 
{
lean_object* v___x_542_; 
lean_dec(v_base_510_);
v___x_542_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10);
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___boxed(lean_object* v_base_543_, lean_object* v_ctorInfo_544_, lean_object* v_field_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_base_543_, v_ctorInfo_544_, v_field_545_);
lean_dec_ref(v_ctorInfo_544_);
return v_res_546_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(lean_object* v_arg_547_, lean_object* v_a_548_){
_start:
{
uint8_t v___x_550_; uint8_t v___x_551_; lean_object* v___x_552_; lean_object* v_subst_553_; lean_object* v___x_554_; 
v___x_550_ = 0;
v___x_551_ = 1;
v___x_552_ = lean_st_ref_get(v_a_548_);
v_subst_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc_ref(v_subst_553_);
lean_dec(v___x_552_);
v___x_554_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v___x_550_, v_subst_553_, v_arg_547_, v___x_551_);
lean_dec_ref(v_subst_553_);
if (lean_obj_tag(v___x_554_) == 1)
{
lean_object* v_fvarId_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_fvarId_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_563_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_fvarId_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_fvarId_555_);
v___x_560_ = v_reuseFailAlloc_562_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v___x_554_);
v___x_564_ = lean_box(0);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_547_ = stack[0].m_obj;
lean_object* v_a_548_ = stack[1].m_obj;
lean_object* v_res_566_;
v_res_566_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_547_, v_a_548_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg___boxed(lean_object* v_arg_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_567_, v_a_568_);
lean_dec(v_a_568_);
return v_res_570_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(lean_object* v_arg_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_571_, v_a_572_);
return v___x_578_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_571_ = stack[0].m_obj;
lean_object* v_a_572_ = stack[1].m_obj;
lean_object* v_a_573_ = stack[2].m_obj;
lean_object* v_a_574_ = stack[3].m_obj;
lean_object* v_a_575_ = stack[4].m_obj;
lean_object* v_a_576_ = stack[5].m_obj;
lean_object* v_res_579_;
v_res_579_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(v_arg_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
stack->m_obj
 = v_res_579_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___boxed(lean_object* v_arg_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(v_arg_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(lean_object* v_msg_588_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = l_Lean_instInhabitedExpr;
v___x_590_ = lean_panic_fn_borrowed(v___x_589_, v_msg_588_);
return v___x_590_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_594_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2));
v___x_595_ = lean_unsigned_to_nat(11u);
v___x_596_ = lean_unsigned_to_nat(83u);
v___x_597_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1));
v___x_598_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_599_ = l_mkPanicMessageWithDecl(v___x_598_, v___x_597_, v___x_596_, v___x_595_, v___x_594_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_box(0);
v___x_601_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_602_ = l_Lean_mkConst(v___x_601_, v___x_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(lean_object* v_type_603_, lean_object* v_arity_604_){
_start:
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = lean_nat_dec_eq(v_arity_604_, v___x_608_);
if (v___x_609_ == 0)
{
switch(lean_obj_tag(v_type_603_))
{
case 7:
{
lean_object* v_body_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_body_610_ = lean_ctor_get(v_type_603_, 2);
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_sub(v_arity_604_, v___x_611_);
lean_dec(v_arity_604_);
v_type_603_ = v_body_610_;
v_arity_604_ = v___x_612_;
goto _start;
}
case 4:
{
lean_object* v_declName_614_; 
lean_dec(v_arity_604_);
v_declName_614_ = lean_ctor_get(v_type_603_, 0);
if (lean_obj_tag(v_declName_614_) == 1)
{
lean_object* v_pre_615_; 
v_pre_615_ = lean_ctor_get(v_declName_614_, 0);
if (lean_obj_tag(v_pre_615_) == 0)
{
lean_object* v_str_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_str_616_ = lean_ctor_get(v_declName_614_, 1);
v___x_617_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0));
v___x_618_ = lean_string_dec_eq(v_str_616_, v___x_617_);
if (v___x_618_ == 0)
{
goto v___jp_605_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4);
return v___x_619_;
}
}
else
{
goto v___jp_605_;
}
}
else
{
goto v___jp_605_;
}
}
default: 
{
lean_dec(v_arity_604_);
goto v___jp_605_;
}
}
}
else
{
lean_dec(v_arity_604_);
lean_inc_ref(v_type_603_);
return v_type_603_;
}
v___jp_605_:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3);
v___x_607_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(v___x_606_);
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___boxed(lean_object* v_type_620_, lean_object* v_arity_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_620_, v_arity_621_);
lean_dec_ref(v_type_620_);
return v_res_622_;
}
}
lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object* v_type_623_, lean_object* v_arity_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_623_, v_arity_624_);
v___x_629_ = l_Lean_Compiler_LCNF_toImpureType(v___x_628_, v_a_625_, v_a_626_);
return v___x_629_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_lowerResultType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_623_ = stack[0].m_obj;
lean_object* v_arity_624_ = stack[1].m_obj;
lean_object* v_a_625_ = stack[2].m_obj;
lean_object* v_a_626_ = stack[3].m_obj;
lean_object* v_res_630_;
v_res_630_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_623_, v_arity_624_, v_a_625_, v_a_626_);
stack->m_obj
 = v_res_630_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType___boxed(lean_object* v_type_631_, lean_object* v_arity_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_631_, v_arity_632_, v_a_633_, v_a_634_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec_ref(v_type_631_);
return v_res_636_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_box(0);
v___x_641_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1));
v___x_642_ = l_Lean_Expr_const___override(v___x_641_, v___x_640_);
return v___x_642_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_box(0);
v___x_647_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4));
v___x_648_ = l_Lean_Expr_const___override(v___x_647_, v___x_646_);
return v___x_648_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = lean_box(0);
v___x_653_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7));
v___x_654_ = l_Lean_Expr_const___override(v___x_653_, v___x_652_);
return v___x_654_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_658_ = lean_box(0);
v___x_659_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10));
v___x_660_ = l_Lean_Expr_const___override(v___x_659_, v___x_658_);
return v___x_660_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_664_ = lean_box(0);
v___x_665_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13));
v___x_666_ = l_Lean_Expr_const___override(v___x_665_, v___x_664_);
return v___x_666_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = lean_box(0);
v___x_671_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16));
v___x_672_ = l_Lean_Expr_const___override(v___x_671_, v___x_670_);
return v___x_672_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = lean_box(0);
v___x_677_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19));
v___x_678_ = l_Lean_Expr_const___override(v___x_677_, v___x_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(lean_object* v_v_679_){
_start:
{
switch(lean_obj_tag(v_v_679_))
{
case 0:
{
lean_object* v_val_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_val_680_ = lean_ctor_get(v_v_679_, 0);
v___x_681_ = lean_cstr_to_nat("4294967296");
v___x_682_ = lean_nat_dec_lt(v_val_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
v___x_683_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
return v___x_683_;
}
else
{
lean_object* v___x_684_; 
v___x_684_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
return v___x_684_;
}
}
case 1:
{
lean_object* v___x_685_; 
v___x_685_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
return v___x_685_;
}
case 2:
{
lean_object* v___x_686_; 
v___x_686_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11);
return v___x_686_;
}
case 3:
{
lean_object* v___x_687_; 
v___x_687_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14);
return v___x_687_;
}
case 4:
{
lean_object* v___x_688_; 
v___x_688_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17);
return v___x_688_;
}
case 5:
{
lean_object* v___x_689_; 
v___x_689_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20);
return v___x_689_;
}
default: 
{
lean_object* v___x_690_; 
v___x_690_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
return v___x_690_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___boxed(lean_object* v_v_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_v_691_);
lean_dec_ref(v_v_691_);
return v_res_692_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(lean_object* v_as_693_, size_t v_i_694_, size_t v_stop_695_, lean_object* v_b_696_){
_start:
{
lean_object* v___y_698_; uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_eq(v_i_694_, v_stop_695_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v_snd_704_; uint8_t v___x_705_; 
v___x_703_ = lean_array_uget_borrowed(v_as_693_, v_i_694_);
v_snd_704_ = lean_ctor_get(v___x_703_, 1);
v___x_705_ = lean_unbox(v_snd_704_);
if (v___x_705_ == 0)
{
v___y_698_ = v_b_696_;
goto v___jp_697_;
}
else
{
lean_object* v_fst_706_; lean_object* v___x_707_; 
v_fst_706_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_fst_706_);
v___x_707_ = lean_array_push(v_b_696_, v_fst_706_);
v___y_698_ = v___x_707_;
goto v___jp_697_;
}
}
else
{
return v_b_696_;
}
v___jp_697_:
{
size_t v___x_699_; size_t v___x_700_; 
v___x_699_ = ((size_t)1ULL);
v___x_700_ = lean_usize_add(v_i_694_, v___x_699_);
v_i_694_ = v___x_700_;
v_b_696_ = v___y_698_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_693_ = stack[0].m_obj;
size_t v_i_694_ = stack[1].m_num;
size_t v_stop_695_ = stack[2].m_num;
lean_object* v_b_696_ = stack[3].m_obj;
lean_object* v_res_708_;
v_res_708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v_as_693_, v_i_694_, v_stop_695_, v_b_696_);
stack->m_obj
 = v_res_708_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4___boxed(lean_object* v_as_709_, lean_object* v_i_710_, lean_object* v_stop_711_, lean_object* v_b_712_){
_start:
{
size_t v_i_boxed_713_; size_t v_stop_boxed_714_; lean_object* v_res_715_; 
v_i_boxed_713_ = lean_unbox_usize(v_i_710_);
lean_dec(v_i_710_);
v_stop_boxed_714_ = lean_unbox_usize(v_stop_711_);
lean_dec(v_stop_711_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v_as_709_, v_i_boxed_713_, v_stop_boxed_714_, v_b_712_);
lean_dec_ref(v_as_709_);
return v_res_715_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_716_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(lean_object* v_msg_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; lean_object* v_toApplicative_725_; lean_object* v_toFunctor_726_; lean_object* v_toSeq_727_; lean_object* v_toSeqLeft_728_; lean_object* v_toSeqRight_729_; lean_object* v___f_730_; lean_object* v___f_731_; lean_object* v___f_732_; lean_object* v___f_733_; lean_object* v___x_734_; lean_object* v___f_735_; lean_object* v___f_736_; lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_toApplicative_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_773_; 
v___x_724_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_725_ = lean_ctor_get(v___x_724_, 0);
v_toFunctor_726_ = lean_ctor_get(v_toApplicative_725_, 0);
v_toSeq_727_ = lean_ctor_get(v_toApplicative_725_, 2);
v_toSeqLeft_728_ = lean_ctor_get(v_toApplicative_725_, 3);
v_toSeqRight_729_ = lean_ctor_get(v_toApplicative_725_, 4);
v___f_730_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_731_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref_n(v_toFunctor_726_, 2);
v___f_732_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_732_, 0, v_toFunctor_726_);
v___f_733_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_733_, 0, v_toFunctor_726_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___f_732_);
lean_ctor_set(v___x_734_, 1, v___f_733_);
lean_inc(v_toSeqRight_729_);
v___f_735_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_735_, 0, v_toSeqRight_729_);
lean_inc(v_toSeqLeft_728_);
v___f_736_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_736_, 0, v_toSeqLeft_728_);
lean_inc(v_toSeq_727_);
v___f_737_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_737_, 0, v_toSeq_727_);
v___x_738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_738_, 0, v___x_734_);
lean_ctor_set(v___x_738_, 1, v___f_730_);
lean_ctor_set(v___x_738_, 2, v___f_737_);
lean_ctor_set(v___x_738_, 3, v___f_736_);
lean_ctor_set(v___x_738_, 4, v___f_735_);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v___f_731_);
v___x_740_ = l_StateRefT_x27_instMonad___redArg(v___x_739_);
v_toApplicative_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v___x_740_, 1);
lean_dec(v_unused_774_);
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_773_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_toApplicative_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_773_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v_toFunctor_745_; lean_object* v_toSeq_746_; lean_object* v_toSeqLeft_747_; lean_object* v_toSeqRight_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_771_; 
v_toFunctor_745_ = lean_ctor_get(v_toApplicative_741_, 0);
v_toSeq_746_ = lean_ctor_get(v_toApplicative_741_, 2);
v_toSeqLeft_747_ = lean_ctor_get(v_toApplicative_741_, 3);
v_toSeqRight_748_ = lean_ctor_get(v_toApplicative_741_, 4);
v_isSharedCheck_771_ = !lean_is_exclusive(v_toApplicative_741_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v_toApplicative_741_, 1);
lean_dec(v_unused_772_);
v___x_750_ = v_toApplicative_741_;
v_isShared_751_ = v_isSharedCheck_771_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_toSeqRight_748_);
lean_inc(v_toSeqLeft_747_);
lean_inc(v_toSeq_746_);
lean_inc(v_toFunctor_745_);
lean_dec(v_toApplicative_741_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_771_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___x_756_; lean_object* v___f_757_; lean_object* v___f_758_; lean_object* v___f_759_; lean_object* v___x_761_; 
v___f_752_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_753_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_745_);
v___f_754_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_754_, 0, v_toFunctor_745_);
v___f_755_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_755_, 0, v_toFunctor_745_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___f_754_);
lean_ctor_set(v___x_756_, 1, v___f_755_);
v___f_757_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_757_, 0, v_toSeqRight_748_);
v___f_758_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_758_, 0, v_toSeqLeft_747_);
v___f_759_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_759_, 0, v_toSeq_746_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 4, v___f_757_);
lean_ctor_set(v___x_750_, 3, v___f_758_);
lean_ctor_set(v___x_750_, 2, v___f_759_);
lean_ctor_set(v___x_750_, 1, v___f_752_);
lean_ctor_set(v___x_750_, 0, v___x_756_);
v___x_761_ = v___x_750_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___f_752_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v___f_759_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v___f_758_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v___f_757_);
v___x_761_ = v_reuseFailAlloc_770_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_763_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___f_753_);
lean_ctor_set(v___x_743_, 0, v___x_761_);
v___x_763_ = v___x_743_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___f_753_);
v___x_763_ = v_reuseFailAlloc_769_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_34977__overap_767_; lean_object* v___x_768_; 
v___x_764_ = l_StateRefT_x27_instMonad___redArg(v___x_763_);
v___x_765_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0);
v___x_766_ = l_instInhabitedOfMonad___redArg(v___x_764_, v___x_765_);
v___x_34977__overap_767_ = lean_panic_fn_borrowed(v___x_766_, v_msg_717_);
lean_dec(v___x_766_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
lean_inc(v___y_718_);
v___x_768_ = lean_apply_6(v___x_34977__overap_767_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, lean_box(0));
return v___x_768_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_717_ = stack[0].m_obj;
lean_object* v___y_718_ = stack[1].m_obj;
lean_object* v___y_719_ = stack[2].m_obj;
lean_object* v___y_720_ = stack[3].m_obj;
lean_object* v___y_721_ = stack[4].m_obj;
lean_object* v___y_722_ = stack[5].m_obj;
lean_object* v_res_775_;
v_res_775_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v_msg_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
stack->m_obj
 = v_res_775_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(lean_object* v_msg_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v_msg_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
return v_res_783_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_784_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(lean_object* v_upperBound_785_, lean_object* v_params_786_, lean_object* v___x_787_, lean_object* v_discr_788_, lean_object* v_a_789_, lean_object* v_b_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_a_794_; uint8_t v___x_798_; 
v___x_798_ = lean_nat_dec_lt(v_a_789_, v_upperBound_785_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
lean_dec(v_a_789_);
lean_dec(v_discr_788_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v_b_790_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_800_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0);
v___x_801_ = lean_box(0);
v___x_802_ = lean_array_get_borrowed(v___x_800_, v_params_786_, v_a_789_);
v___x_803_ = lean_nat_dec_eq(v_a_789_, v___x_787_);
if (v___x_803_ == 0)
{
lean_object* v_fvarId_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v_subst_807_; lean_object* v_jpParamMask_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_817_; 
v_fvarId_804_ = lean_ctor_get(v___x_802_, 0);
v___x_805_ = lean_box(0);
v___x_806_ = lean_st_ref_take(v___y_791_);
v_subst_807_ = lean_ctor_get(v___x_806_, 0);
v_jpParamMask_808_ = lean_ctor_get(v___x_806_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_817_ == 0)
{
v___x_810_ = v___x_806_;
v_isShared_811_ = v_isSharedCheck_817_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_jpParamMask_808_);
lean_inc(v_subst_807_);
lean_dec(v___x_806_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_817_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
lean_inc(v_fvarId_804_);
v___x_812_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_807_, v_fvarId_804_, v___x_805_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_812_);
v___x_814_ = v___x_810_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_jpParamMask_808_);
v___x_814_ = v_reuseFailAlloc_816_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; 
v___x_815_ = lean_st_ref_put(v___y_791_, v___x_814_);
v_a_794_ = v___x_801_;
goto v___jp_793_;
}
}
}
else
{
lean_object* v_fvarId_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_subst_821_; lean_object* v_jpParamMask_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_831_; 
v_fvarId_818_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_discr_788_);
v___x_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_819_, 0, v_discr_788_);
v___x_820_ = lean_st_ref_take(v___y_791_);
v_subst_821_ = lean_ctor_get(v___x_820_, 0);
v_jpParamMask_822_ = lean_ctor_get(v___x_820_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_831_ == 0)
{
v___x_824_ = v___x_820_;
v_isShared_825_ = v_isSharedCheck_831_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_jpParamMask_822_);
lean_inc(v_subst_821_);
lean_dec(v___x_820_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_831_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
lean_inc(v_fvarId_818_);
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_821_, v_fvarId_818_, v___x_819_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_826_);
v___x_828_ = v___x_824_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_jpParamMask_822_);
v___x_828_ = v_reuseFailAlloc_830_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; 
v___x_829_ = lean_st_ref_put(v___y_791_, v___x_828_);
v_a_794_ = v___x_801_;
goto v___jp_793_;
}
}
}
}
v___jp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_unsigned_to_nat(1u);
v___x_796_ = lean_nat_add(v_a_789_, v___x_795_);
lean_dec(v_a_789_);
v_a_789_ = v___x_796_;
v_b_790_ = v_a_794_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_785_ = stack[0].m_obj;
lean_object* v_params_786_ = stack[1].m_obj;
lean_object* v___x_787_ = stack[2].m_obj;
lean_object* v_discr_788_ = stack[3].m_obj;
lean_object* v_a_789_ = stack[4].m_obj;
lean_object* v_b_790_ = stack[5].m_obj;
lean_object* v___y_791_ = stack[6].m_obj;
lean_object* v_res_832_;
v_res_832_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_785_, v_params_786_, v___x_787_, v_discr_788_, v_a_789_, v_b_790_, v___y_791_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(lean_object* v_upperBound_833_, lean_object* v_params_834_, lean_object* v___x_835_, lean_object* v_discr_836_, lean_object* v_a_837_, lean_object* v_b_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_833_, v_params_834_, v___x_835_, v_discr_836_, v_a_837_, v_b_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec(v___x_835_);
lean_dec_ref(v_params_834_);
lean_dec(v_upperBound_833_);
return v_res_841_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(size_t v_sz_842_, size_t v_i_843_, lean_object* v_bs_844_){
_start:
{
uint8_t v___x_845_; 
v___x_845_ = lean_usize_dec_lt(v_i_843_, v_sz_842_);
if (v___x_845_ == 0)
{
return v_bs_844_;
}
else
{
lean_object* v_v_846_; lean_object* v_type_847_; lean_object* v___x_848_; lean_object* v_bs_x27_849_; uint8_t v___y_851_; uint8_t v___y_858_; uint8_t v___x_860_; 
v_v_846_ = lean_array_uget_borrowed(v_bs_844_, v_i_843_);
v_type_847_ = lean_ctor_get(v_v_846_, 2);
lean_inc_ref(v_type_847_);
v___x_848_ = lean_unsigned_to_nat(0u);
v_bs_x27_849_ = lean_array_uset(v_bs_844_, v_i_843_, v___x_848_);
v___x_860_ = l_Lean_Expr_isVoid(v_type_847_);
if (v___x_860_ == 0)
{
uint8_t v___x_861_; 
v___x_861_ = l_Lean_Expr_isErased(v_type_847_);
lean_dec_ref(v_type_847_);
v___y_858_ = v___x_861_;
goto v___jp_857_;
}
else
{
lean_dec_ref(v_type_847_);
v___y_858_ = v___x_860_;
goto v___jp_857_;
}
v___jp_850_:
{
size_t v___x_852_; size_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_852_ = ((size_t)1ULL);
v___x_853_ = lean_usize_add(v_i_843_, v___x_852_);
v___x_854_ = lean_box(v___y_851_);
v___x_855_ = lean_array_uset(v_bs_x27_849_, v_i_843_, v___x_854_);
v_i_843_ = v___x_853_;
v_bs_844_ = v___x_855_;
goto _start;
}
v___jp_857_:
{
if (v___y_858_ == 0)
{
v___y_851_ = v___x_845_;
goto v___jp_850_;
}
else
{
uint8_t v___x_859_; 
v___x_859_ = 0;
v___y_851_ = v___x_859_;
goto v___jp_850_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_842_ = stack[0].m_num;
size_t v_i_843_ = stack[1].m_num;
lean_object* v_bs_844_ = stack[2].m_obj;
lean_object* v_res_862_;
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_842_, v_i_843_, v_bs_844_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object* v_sz_863_, lean_object* v_i_864_, lean_object* v_bs_865_){
_start:
{
size_t v_sz_boxed_866_; size_t v_i_boxed_867_; lean_object* v_res_868_; 
v_sz_boxed_866_ = lean_unbox_usize(v_sz_863_);
lean_dec(v_sz_863_);
v_i_boxed_867_ = lean_unbox_usize(v_i_864_);
lean_dec(v_i_864_);
v_res_868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_boxed_866_, v_i_boxed_867_, v_bs_865_);
return v_res_868_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_869_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_872_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_873_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1);
v___x_874_ = lean_unsigned_to_nat(0u);
v___x_875_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
lean_ctor_set(v___x_875_, 2, v___x_874_);
lean_ctor_set(v___x_875_, 3, v___x_874_);
lean_ctor_set(v___x_875_, 4, v___x_873_);
lean_ctor_set(v___x_875_, 5, v___x_873_);
lean_ctor_set(v___x_875_, 6, v___x_873_);
lean_ctor_set(v___x_875_, 7, v___x_873_);
lean_ctor_set(v___x_875_, 8, v___x_873_);
lean_ctor_set(v___x_875_, 9, v___x_873_);
lean_ctor_set(v___x_875_, 10, v___x_873_);
lean_ctor_set(v___x_875_, 11, v___x_872_);
return v___x_875_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(lean_object* v_msg_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_ref_882_; lean_object* v___x_883_; lean_object* v_env_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_ref_882_ = lean_ctor_get(v___y_879_, 2);
v___x_883_ = lean_st_ref_get(v___y_880_);
v_env_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc_ref(v_env_884_);
lean_dec(v___x_883_);
v___x_885_ = lean_st_ref_get(v___y_878_);
v___x_886_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_877_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_909_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_909_ == 0)
{
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_909_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_909_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_lctx_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_907_; 
v_lctx_891_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v___x_885_, 1);
lean_dec(v_unused_908_);
v___x_893_ = v___x_885_;
v_isShared_894_ = v_isSharedCheck_907_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_lctx_891_);
lean_dec(v___x_885_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_907_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_895_ = lean_unbox(v_a_887_);
lean_dec(v_a_887_);
v___x_896_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_891_, v___x_895_);
lean_dec_ref(v_lctx_891_);
v___x_897_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_879_);
v___x_898_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2);
v___x_899_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_899_, 0, v_env_884_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
lean_ctor_set(v___x_899_, 2, v___x_896_);
lean_ctor_set(v___x_899_, 3, v___x_897_);
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 3);
lean_ctor_set(v___x_893_, 1, v_msg_876_);
lean_ctor_set(v___x_893_, 0, v___x_899_);
v___x_901_ = v___x_893_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_msg_876_);
v___x_901_ = v_reuseFailAlloc_906_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; lean_object* v___x_904_; 
lean_inc(v_ref_882_);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v_ref_882_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
if (v_isShared_890_ == 0)
{
lean_ctor_set_tag(v___x_889_, 1);
lean_ctor_set(v___x_889_, 0, v___x_902_);
v___x_904_ = v___x_889_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v___x_885_);
lean_dec_ref(v_env_884_);
lean_dec_ref(v_msg_876_);
v_a_910_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_886_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_886_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_876_ = stack[0].m_obj;
lean_object* v___y_877_ = stack[1].m_obj;
lean_object* v___y_878_ = stack[2].m_obj;
lean_object* v___y_879_ = stack[3].m_obj;
lean_object* v___y_880_ = stack[4].m_obj;
lean_object* v_res_918_;
v_res_918_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
stack->m_obj
 = v_res_918_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(lean_object* v_msg_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_925_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(size_t v_sz_926_, size_t v_i_927_, lean_object* v_bs_928_, lean_object* v___y_929_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = lean_usize_dec_lt(v_i_927_, v_sz_926_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v_bs_928_);
return v___x_932_;
}
else
{
lean_object* v_v_933_; lean_object* v___x_934_; lean_object* v_bs_x27_935_; lean_object* v___x_936_; 
v_v_933_ = lean_array_uget(v_bs_928_, v_i_927_);
v___x_934_ = lean_unsigned_to_nat(0u);
v_bs_x27_935_ = lean_array_uset(v_bs_928_, v_i_927_, v___x_934_);
v___x_936_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_v_933_, v___y_929_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; size_t v___x_938_; size_t v___x_939_; lean_object* v___x_940_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_936_, 1);
v___x_938_ = ((size_t)1ULL);
v___x_939_ = lean_usize_add(v_i_927_, v___x_938_);
v___x_940_ = lean_array_uset(v_bs_x27_935_, v_i_927_, v_a_937_);
v_i_927_ = v___x_939_;
v_bs_928_ = v___x_940_;
goto _start;
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec_ref(v_bs_x27_935_);
v_a_942_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_936_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_936_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_926_ = stack[0].m_num;
size_t v_i_927_ = stack[1].m_num;
lean_object* v_bs_928_ = stack[2].m_obj;
lean_object* v___y_929_ = stack[3].m_obj;
lean_object* v_res_950_;
v_res_950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_926_, v_i_927_, v_bs_928_, v___y_929_);
stack->m_obj
 = v_res_950_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg___boxed(lean_object* v_sz_951_, lean_object* v_i_952_, lean_object* v_bs_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
size_t v_sz_boxed_956_; size_t v_i_boxed_957_; lean_object* v_res_958_; 
v_sz_boxed_956_ = lean_unbox_usize(v_sz_951_);
lean_dec(v_sz_951_);
v_i_boxed_957_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_res_958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_boxed_956_, v_i_boxed_957_, v_bs_953_, v___y_954_);
lean_dec(v___y_954_);
return v_res_958_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(lean_object* v_upperBound_959_, lean_object* v_fieldInfo_960_, lean_object* v___x_961_, lean_object* v_a_962_, lean_object* v_b_963_){
_start:
{
lean_object* v_a_966_; uint8_t v___x_970_; 
v___x_970_ = lean_nat_dec_lt(v_a_962_, v_upperBound_959_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
lean_dec(v_a_962_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v_b_963_);
return v___x_971_;
}
else
{
lean_object* v___x_972_; 
v___x_972_ = lean_array_fget_borrowed(v_fieldInfo_960_, v_a_962_);
if (lean_obj_tag(v___x_972_) == 1)
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = lean_box(0);
v___x_974_ = lean_array_get_borrowed(v___x_973_, v___x_961_, v_a_962_);
lean_inc(v___x_974_);
v___x_975_ = lean_array_push(v_b_963_, v___x_974_);
v_a_966_ = v___x_975_;
goto v___jp_965_;
}
else
{
v_a_966_ = v_b_963_;
goto v___jp_965_;
}
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_nat_add(v_a_962_, v___x_967_);
lean_dec(v_a_962_);
v_a_962_ = v___x_968_;
v_b_963_ = v_a_966_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_959_ = stack[0].m_obj;
lean_object* v_fieldInfo_960_ = stack[1].m_obj;
lean_object* v___x_961_ = stack[2].m_obj;
lean_object* v_a_962_ = stack[3].m_obj;
lean_object* v_b_963_ = stack[4].m_obj;
lean_object* v_res_976_;
v_res_976_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_959_, v_fieldInfo_960_, v___x_961_, v_a_962_, v_b_963_);
stack->m_obj
 = v_res_976_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(lean_object* v_upperBound_977_, lean_object* v_fieldInfo_978_, lean_object* v___x_979_, lean_object* v_a_980_, lean_object* v_b_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_977_, v_fieldInfo_978_, v___x_979_, v_a_980_, v_b_981_);
lean_dec_ref(v___x_979_);
lean_dec_ref(v_fieldInfo_978_);
lean_dec(v_upperBound_977_);
return v_res_983_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object* v_as_984_, size_t v_i_985_, size_t v_stop_986_, lean_object* v_b_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_a_991_; uint8_t v___x_995_; 
v___x_995_ = lean_usize_dec_eq(v_i_985_, v_stop_986_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v_snd_997_; uint8_t v___x_998_; 
v___x_996_ = lean_array_uget_borrowed(v_as_984_, v_i_985_);
v_snd_997_ = lean_ctor_get(v___x_996_, 1);
v___x_998_ = lean_unbox(v_snd_997_);
if (v___x_998_ == 0)
{
v_a_991_ = v_b_987_;
goto v___jp_990_;
}
else
{
lean_object* v_fst_999_; lean_object* v___x_1000_; 
v_fst_999_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_fst_999_);
v___x_1000_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_fst_999_, v___y_988_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = lean_array_push(v_b_987_, v_a_1001_);
v_a_991_ = v___x_1002_;
goto v___jp_990_;
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v_b_987_);
v_a_1003_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1000_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1000_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
else
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v_b_987_);
return v___x_1011_;
}
v___jp_990_:
{
size_t v___x_992_; size_t v___x_993_; 
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_add(v_i_985_, v___x_992_);
v_i_985_ = v___x_993_;
v_b_987_ = v_a_991_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_984_ = stack[0].m_obj;
size_t v_i_985_ = stack[1].m_num;
size_t v_stop_986_ = stack[2].m_num;
lean_object* v_b_987_ = stack[3].m_obj;
lean_object* v___y_988_ = stack[4].m_obj;
lean_object* v_res_1012_;
v_res_1012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_984_, v_i_985_, v_stop_986_, v_b_987_, v___y_988_);
stack->m_obj
 = v_res_1012_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object* v_as_1013_, lean_object* v_i_1014_, lean_object* v_stop_1015_, lean_object* v_b_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
size_t v_i_boxed_1019_; size_t v_stop_boxed_1020_; lean_object* v_res_1021_; 
v_i_boxed_1019_ = lean_unbox_usize(v_i_1014_);
lean_dec(v_i_1014_);
v_stop_boxed_1020_ = lean_unbox_usize(v_stop_1015_);
lean_dec(v_stop_1015_);
v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_1013_, v_i_boxed_1019_, v_stop_boxed_1020_, v_b_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v_as_1013_);
return v_res_1021_;
}
}
static lean_object* _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0(void){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Array_instInhabited___redArg();
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(lean_object* v_msg_1023_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_obj_once(&l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0, &l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0_once, _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0);
v___x_1025_ = lean_panic_fn_borrowed(v___x_1024_, v_msg_1023_);
return v___x_1025_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1029_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2));
v___x_1030_ = lean_unsigned_to_nat(11u);
v___x_1031_ = lean_unsigned_to_nat(163u);
v___x_1032_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1));
v___x_1033_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0));
v___x_1034_ = l_mkPanicMessageWithDecl(v___x_1033_, v___x_1032_, v___x_1031_, v___x_1030_, v___x_1029_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(lean_object* v_a_1035_, lean_object* v_x_1036_){
_start:
{
if (lean_obj_tag(v_x_1036_) == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3);
v___x_1038_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(v___x_1037_);
return v___x_1038_;
}
else
{
lean_object* v_key_1039_; lean_object* v_value_1040_; lean_object* v_tail_1041_; uint8_t v___x_1042_; 
v_key_1039_ = lean_ctor_get(v_x_1036_, 0);
v_value_1040_ = lean_ctor_get(v_x_1036_, 1);
v_tail_1041_ = lean_ctor_get(v_x_1036_, 2);
v___x_1042_ = l_Lean_instBEqFVarId_beq(v_key_1039_, v_a_1035_);
if (v___x_1042_ == 0)
{
v_x_1036_ = v_tail_1041_;
goto _start;
}
else
{
lean_inc(v_value_1040_);
return v_value_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___boxed(lean_object* v_a_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_a_1044_, v_x_1045_);
lean_dec(v_x_1045_);
lean_dec(v_a_1044_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(lean_object* v_m_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_buckets_1049_; lean_object* v___x_1050_; uint64_t v___x_1051_; uint64_t v___x_1052_; uint64_t v___x_1053_; uint64_t v_fold_1054_; uint64_t v___x_1055_; uint64_t v___x_1056_; uint64_t v___x_1057_; size_t v___x_1058_; size_t v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; size_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_buckets_1049_ = lean_ctor_get(v_m_1047_, 1);
v___x_1050_ = lean_array_get_size(v_buckets_1049_);
v___x_1051_ = l_Lean_instHashableFVarId_hash(v_a_1048_);
v___x_1052_ = 32ULL;
v___x_1053_ = lean_uint64_shift_right(v___x_1051_, v___x_1052_);
v_fold_1054_ = lean_uint64_xor(v___x_1051_, v___x_1053_);
v___x_1055_ = 16ULL;
v___x_1056_ = lean_uint64_shift_right(v_fold_1054_, v___x_1055_);
v___x_1057_ = lean_uint64_xor(v_fold_1054_, v___x_1056_);
v___x_1058_ = lean_uint64_to_usize(v___x_1057_);
v___x_1059_ = lean_usize_of_nat(v___x_1050_);
v___x_1060_ = ((size_t)1ULL);
v___x_1061_ = lean_usize_sub(v___x_1059_, v___x_1060_);
v___x_1062_ = lean_usize_land(v___x_1058_, v___x_1061_);
v___x_1063_ = lean_array_uget_borrowed(v_buckets_1049_, v___x_1062_);
v___x_1064_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_a_1048_, v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(lean_object* v_m_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_m_1065_, v_a_1066_);
lean_dec(v_a_1066_);
lean_dec_ref(v_m_1065_);
return v_res_1067_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(size_t v_sz_1068_, size_t v_i_1069_, lean_object* v_bs_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_usize_dec_lt(v_i_1069_, v_sz_1068_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v_bs_1070_);
return v___x_1077_;
}
else
{
lean_object* v_v_1078_; lean_object* v___x_1079_; lean_object* v_bs_x27_1080_; lean_object* v___x_1081_; 
v_v_1078_ = lean_array_uget(v_bs_1070_, v_i_1069_);
v___x_1079_ = lean_unsigned_to_nat(0u);
v_bs_x27_1080_ = lean_array_uset(v_bs_1070_, v_i_1069_, v___x_1079_);
v___x_1081_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_v_1078_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; size_t v___x_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_add(v_i_1069_, v___x_1083_);
v___x_1085_ = lean_array_uset(v_bs_x27_1080_, v_i_1069_, v_a_1082_);
v_i_1069_ = v___x_1084_;
v_bs_1070_ = v___x_1085_;
goto _start;
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v_bs_x27_1080_);
v_a_1087_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1081_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1081_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1068_ = stack[0].m_num;
size_t v_i_1069_ = stack[1].m_num;
lean_object* v_bs_1070_ = stack[2].m_obj;
lean_object* v___y_1071_ = stack[3].m_obj;
lean_object* v___y_1072_ = stack[4].m_obj;
lean_object* v___y_1073_ = stack[5].m_obj;
lean_object* v___y_1074_ = stack[6].m_obj;
lean_object* v_res_1095_;
v_res_1095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_1068_, v_i_1069_, v_bs_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
stack->m_obj
 = v_res_1095_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(lean_object* v_sz_1096_, lean_object* v_i_1097_, lean_object* v_bs_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
size_t v_sz_boxed_1104_; size_t v_i_boxed_1105_; lean_object* v_res_1106_; 
v_sz_boxed_1104_ = lean_unbox_usize(v_sz_1096_);
lean_dec(v_sz_1096_);
v_i_boxed_1105_ = lean_unbox_usize(v_i_1097_);
lean_dec(v_i_1097_);
v_res_1106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_boxed_1104_, v_i_boxed_1105_, v_bs_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec(v___y_1099_);
return v_res_1106_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1109_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1));
v___x_1110_ = lean_unsigned_to_nat(12u);
v___x_1111_ = lean_unsigned_to_nat(116u);
v___x_1112_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1113_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1114_ = l_mkPanicMessageWithDecl(v___x_1113_, v___x_1112_, v___x_1111_, v___x_1110_, v___x_1109_);
return v___x_1114_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(lean_object* v_k_1115_, lean_object* v_decl_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___x_1123_; lean_object* v_lctx_1124_; lean_object* v_nextIdx_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1145_; 
v___x_1123_ = lean_st_ref_take(v_a_1119_);
v_lctx_1124_ = lean_ctor_get(v___x_1123_, 0);
v_nextIdx_1125_ = lean_ctor_get(v___x_1123_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1127_ = v___x_1123_;
v_isShared_1128_ = v_isSharedCheck_1145_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_nextIdx_1125_);
lean_inc(v_lctx_1124_);
lean_dec(v___x_1123_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1145_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1129_ = 1;
lean_inc_ref(v_decl_1116_);
v___x_1130_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1129_, v_lctx_1124_, v_decl_1116_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1130_);
v___x_1132_ = v___x_1127_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_nextIdx_1125_);
v___x_1132_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_st_ref_put(v_a_1119_, v___x_1132_);
v___x_1134_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1115_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_decl_1116_);
lean_ctor_set(v___x_1139_, 1, v_a_1135_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
lean_dec_ref(v_decl_1116_);
return v___x_1134_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1115_ = stack[0].m_obj;
lean_object* v_decl_1116_ = stack[1].m_obj;
lean_object* v_a_1117_ = stack[2].m_obj;
lean_object* v_a_1118_ = stack[3].m_obj;
lean_object* v_a_1119_ = stack[4].m_obj;
lean_object* v_a_1120_ = stack[5].m_obj;
lean_object* v_a_1121_ = stack[6].m_obj;
lean_object* v_res_1146_;
v_res_1146_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1115_, v_decl_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
stack->m_obj
 = v_res_1146_;
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(lean_object* v_k_1147_, lean_object* v_fvarId_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v_subst_1157_; lean_object* v_jpParamMask_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1168_; 
v___x_1155_ = lean_box(0);
v___x_1156_ = lean_st_ref_take(v_a_1149_);
v_subst_1157_ = lean_ctor_get(v___x_1156_, 0);
v_jpParamMask_1158_ = lean_ctor_get(v___x_1156_, 1);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1160_ = v___x_1156_;
v_isShared_1161_ = v_isSharedCheck_1168_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_jpParamMask_1158_);
lean_inc(v_subst_1157_);
lean_dec(v___x_1156_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1168_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1157_, v_fvarId_1148_, v___x_1155_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1162_);
v___x_1164_ = v___x_1160_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_jpParamMask_1158_);
v___x_1164_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_st_ref_put(v_a_1149_, v___x_1164_);
v___x_1166_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1147_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
return v___x_1166_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1147_ = stack[0].m_obj;
lean_object* v_fvarId_1148_ = stack[1].m_obj;
lean_object* v_a_1149_ = stack[2].m_obj;
lean_object* v_a_1150_ = stack[3].m_obj;
lean_object* v_a_1151_ = stack[4].m_obj;
lean_object* v_a_1152_ = stack[5].m_obj;
lean_object* v_a_1153_ = stack[6].m_obj;
lean_object* v_res_1169_;
v_res_1169_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1147_, v_fvarId_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
stack->m_obj
 = v_res_1169_;
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(lean_object* v_decl_1171_, lean_object* v_k_1172_, lean_object* v_name_1173_, lean_object* v_numParams_1174_, lean_object* v_args_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_fvarId_1182_; lean_object* v_binderName_1183_; lean_object* v_type_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1246_; 
v_fvarId_1182_ = lean_ctor_get(v_decl_1171_, 0);
v_binderName_1183_ = lean_ctor_get(v_decl_1171_, 1);
v_type_1184_ = lean_ctor_get(v_decl_1171_, 2);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_decl_1171_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v_decl_1171_, 3);
lean_dec(v_unused_1247_);
v___x_1186_ = v_decl_1171_;
v_isShared_1187_ = v_isSharedCheck_1246_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_type_1184_);
lean_inc(v_binderName_1183_);
lean_inc(v_fvarId_1182_);
lean_dec(v_decl_1171_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1246_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1184_, v_a_1179_, v_a_1180_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
v___x_1190_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1189_);
lean_dec(v_a_1189_);
v___x_1191_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1174_);
v___x_1192_ = l_Array_extract___redArg(v_args_1175_, v___x_1191_, v_numParams_1174_);
v___x_1193_ = lean_array_get_size(v_args_1175_);
v___x_1194_ = l_Array_extract___redArg(v_args_1175_, v_numParams_1174_, v___x_1193_);
v___x_1195_ = 1;
v___x_1196_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0));
lean_inc(v_binderName_1183_);
v___x_1197_ = l_Lean_Name_str___override(v_binderName_1183_, v___x_1196_);
v___x_1198_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1199_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1199_, 0, v_name_1173_);
lean_ctor_set(v___x_1199_, 1, v___x_1192_);
v___x_1200_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1195_, v___x_1197_, v___x_1198_, v___x_1199_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v_fvarId_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v___x_1200_, 1);
v_fvarId_1202_ = lean_ctor_get(v_a_1201_, 0);
lean_inc(v_fvarId_1202_);
v___x_1203_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1203_, 0, v_fvarId_1202_);
lean_ctor_set(v___x_1203_, 1, v___x_1194_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 3, v___x_1203_);
lean_ctor_set(v___x_1186_, 2, v___x_1190_);
v___x_1205_ = v___x_1186_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_fvarId_1182_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_binderName_1183_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v_lctx_1207_; lean_object* v_nextIdx_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1228_; 
v___x_1206_ = lean_st_ref_take(v_a_1178_);
v_lctx_1207_ = lean_ctor_get(v___x_1206_, 0);
v_nextIdx_1208_ = lean_ctor_get(v___x_1206_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1210_ = v___x_1206_;
v_isShared_1211_ = v_isSharedCheck_1228_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_nextIdx_1208_);
lean_inc(v_lctx_1207_);
lean_dec(v___x_1206_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1228_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
lean_inc_ref(v___x_1205_);
v___x_1212_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1195_, v_lctx_1207_, v___x_1205_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v___x_1212_);
v___x_1214_ = v___x_1210_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_nextIdx_1208_);
v___x_1214_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_st_ref_put(v_a_1178_, v___x_1214_);
v___x_1216_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1172_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1226_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1226_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1226_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1205_);
lean_ctor_set(v___x_1221_, 1, v_a_1217_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_a_1201_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1222_);
v___x_1224_ = v___x_1219_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
else
{
lean_dec_ref(v___x_1205_);
lean_dec(v_a_1201_);
return v___x_1216_;
}
}
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1190_);
lean_del_object(v___x_1186_);
lean_dec(v_binderName_1183_);
lean_dec(v_fvarId_1182_);
lean_dec_ref(v_k_1172_);
v_a_1230_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1200_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1200_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_del_object(v___x_1186_);
lean_dec(v_binderName_1183_);
lean_dec(v_fvarId_1182_);
lean_dec(v_numParams_1174_);
lean_dec(v_name_1173_);
lean_dec_ref(v_k_1172_);
v_a_1238_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1188_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1188_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1171_ = stack[0].m_obj;
lean_object* v_k_1172_ = stack[1].m_obj;
lean_object* v_name_1173_ = stack[2].m_obj;
lean_object* v_numParams_1174_ = stack[3].m_obj;
lean_object* v_args_1175_ = stack[4].m_obj;
lean_object* v_a_1176_ = stack[5].m_obj;
lean_object* v_a_1177_ = stack[6].m_obj;
lean_object* v_a_1178_ = stack[7].m_obj;
lean_object* v_a_1179_ = stack[8].m_obj;
lean_object* v_a_1180_ = stack[9].m_obj;
lean_object* v_res_1248_;
v_res_1248_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_1171_, v_k_1172_, v_name_1173_, v_numParams_1174_, v_args_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
stack->m_obj
 = v_res_1248_;
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(lean_object* v_decl_1249_, lean_object* v_k_1250_, lean_object* v_name_1251_, lean_object* v_args_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_fvarId_1259_; lean_object* v_binderName_1260_; lean_object* v_type_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1280_; 
v_fvarId_1259_ = lean_ctor_get(v_decl_1249_, 0);
v_binderName_1260_ = lean_ctor_get(v_decl_1249_, 1);
v_type_1261_ = lean_ctor_get(v_decl_1249_, 2);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_decl_1249_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; 
v_unused_1281_ = lean_ctor_get(v_decl_1249_, 3);
lean_dec(v_unused_1281_);
v___x_1263_ = v_decl_1249_;
v_isShared_1264_ = v_isSharedCheck_1280_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_type_1261_);
lean_inc(v_binderName_1260_);
lean_inc(v_fvarId_1259_);
lean_dec(v_decl_1249_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1280_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1261_, v_a_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1267_, 0, v_name_1251_);
lean_ctor_set(v___x_1267_, 1, v_args_1252_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 3, v___x_1267_);
lean_ctor_set(v___x_1263_, 2, v_a_1266_);
v___x_1269_ = v___x_1263_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_fvarId_1259_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_binderName_1260_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_a_1266_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; 
v___x_1270_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1250_, v___x_1269_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
return v___x_1270_;
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_del_object(v___x_1263_);
lean_dec(v_binderName_1260_);
lean_dec(v_fvarId_1259_);
lean_dec_ref(v_args_1252_);
lean_dec(v_name_1251_);
lean_dec_ref(v_k_1250_);
v_a_1272_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1265_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1265_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1249_ = stack[0].m_obj;
lean_object* v_k_1250_ = stack[1].m_obj;
lean_object* v_name_1251_ = stack[2].m_obj;
lean_object* v_args_1252_ = stack[3].m_obj;
lean_object* v_a_1253_ = stack[4].m_obj;
lean_object* v_a_1254_ = stack[5].m_obj;
lean_object* v_a_1255_ = stack[6].m_obj;
lean_object* v_a_1256_ = stack[7].m_obj;
lean_object* v_a_1257_ = stack[8].m_obj;
lean_object* v_res_1282_;
v_res_1282_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1249_, v_k_1250_, v_name_1251_, v_args_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
stack->m_obj
 = v_res_1282_;
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(lean_object* v_decl_1283_, lean_object* v_k_1284_, lean_object* v_name_1285_, lean_object* v_args_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_fvarId_1293_; lean_object* v_binderName_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1304_; 
v_fvarId_1293_ = lean_ctor_get(v_decl_1283_, 0);
v_binderName_1294_ = lean_ctor_get(v_decl_1283_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_decl_1283_);
if (v_isSharedCheck_1304_ == 0)
{
lean_object* v_unused_1305_; lean_object* v_unused_1306_; 
v_unused_1305_ = lean_ctor_get(v_decl_1283_, 3);
lean_dec(v_unused_1305_);
v_unused_1306_ = lean_ctor_get(v_decl_1283_, 2);
lean_dec(v_unused_1306_);
v___x_1296_ = v_decl_1283_;
v_isShared_1297_ = v_isSharedCheck_1304_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_binderName_1294_);
lean_inc(v_fvarId_1293_);
lean_dec(v_decl_1283_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1304_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1298_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1299_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_1299_, 0, v_name_1285_);
lean_ctor_set(v___x_1299_, 1, v_args_1286_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 3, v___x_1299_);
lean_ctor_set(v___x_1296_, 2, v___x_1298_);
v___x_1301_ = v___x_1296_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_fvarId_1293_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_binderName_1294_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; 
v___x_1302_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1284_, v___x_1301_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
return v___x_1302_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1283_ = stack[0].m_obj;
lean_object* v_k_1284_ = stack[1].m_obj;
lean_object* v_name_1285_ = stack[2].m_obj;
lean_object* v_args_1286_ = stack[3].m_obj;
lean_object* v_a_1287_ = stack[4].m_obj;
lean_object* v_a_1288_ = stack[5].m_obj;
lean_object* v_a_1289_ = stack[6].m_obj;
lean_object* v_a_1290_ = stack[7].m_obj;
lean_object* v_a_1291_ = stack[8].m_obj;
lean_object* v_res_1307_;
v_res_1307_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_1283_, v_k_1284_, v_name_1285_, v_args_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
stack->m_obj
 = v_res_1307_;
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(lean_object* v_decl_1308_, lean_object* v_k_1309_, lean_object* v_name_1310_, lean_object* v_numParams_1311_, lean_object* v_args_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_numArgs_1319_; uint8_t v___x_1320_; 
v_numArgs_1319_ = lean_array_get_size(v_args_1312_);
v___x_1320_ = lean_nat_dec_lt(v_numArgs_1319_, v_numParams_1311_);
if (v___x_1320_ == 0)
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_nat_dec_eq(v_numArgs_1319_, v_numParams_1311_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
v___x_1322_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_1308_, v_k_1309_, v_name_1310_, v_numParams_1311_, v_args_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
lean_dec_ref(v_args_1312_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; 
lean_dec(v_numParams_1311_);
v___x_1323_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1308_, v_k_1309_, v_name_1310_, v_args_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
return v___x_1323_;
}
}
else
{
lean_object* v___x_1324_; 
lean_dec(v_numParams_1311_);
v___x_1324_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_1308_, v_k_1309_, v_name_1310_, v_args_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
return v___x_1324_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1308_ = stack[0].m_obj;
lean_object* v_k_1309_ = stack[1].m_obj;
lean_object* v_name_1310_ = stack[2].m_obj;
lean_object* v_numParams_1311_ = stack[3].m_obj;
lean_object* v_args_1312_ = stack[4].m_obj;
lean_object* v_a_1313_ = stack[5].m_obj;
lean_object* v_a_1314_ = stack[6].m_obj;
lean_object* v_a_1315_ = stack[7].m_obj;
lean_object* v_a_1316_ = stack[8].m_obj;
lean_object* v_a_1317_ = stack[9].m_obj;
lean_object* v_res_1325_;
v_res_1325_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1308_, v_k_1309_, v_name_1310_, v_numParams_1311_, v_args_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
stack->m_obj
 = v_res_1325_;
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1327_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3));
v___x_1328_ = lean_unsigned_to_nat(14u);
v___x_1329_ = lean_unsigned_to_nat(185u);
v___x_1330_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1331_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1332_ = l_mkPanicMessageWithDecl(v___x_1331_, v___x_1330_, v___x_1329_, v___x_1328_, v___x_1327_);
return v___x_1332_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
v___x_1340_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
return v___x_1340_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(lean_object* v_decl_1349_, lean_object* v_k_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v_fvarId_1365_; lean_object* v_binderName_1366_; lean_object* v_type_1367_; lean_object* v_value_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_subst_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1820_; 
v_fvarId_1365_ = lean_ctor_get(v_decl_1349_, 0);
v_binderName_1366_ = lean_ctor_get(v_decl_1349_, 1);
v_type_1367_ = lean_ctor_get(v_decl_1349_, 2);
v_value_1368_ = lean_ctor_get(v_decl_1349_, 3);
v___x_1369_ = lean_box(0);
v___x_1370_ = 0;
v___x_1371_ = 1;
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_st_ref_get(v_a_1351_);
v_subst_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v___x_1373_, 1);
lean_dec(v_unused_1821_);
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1820_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_subst_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1820_;
goto v_resetjp_1375_;
}
v___jp_1357_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2);
v___x_1364_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1363_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
return v___x_1364_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; 
lean_inc(v_value_1368_);
v___x_1378_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v___x_1370_, v_subst_1374_, v_value_1368_, v___x_1371_);
lean_dec_ref(v_subst_1374_);
switch(lean_obj_tag(v___x_1378_))
{
case 0:
{
lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1395_; 
lean_inc(v_binderName_1366_);
lean_inc(v_fvarId_1365_);
lean_del_object(v___x_1376_);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_decl_1349_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; lean_object* v_unused_1397_; lean_object* v_unused_1398_; lean_object* v_unused_1399_; 
v_unused_1396_ = lean_ctor_get(v_decl_1349_, 3);
lean_dec(v_unused_1396_);
v_unused_1397_ = lean_ctor_get(v_decl_1349_, 2);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_decl_1349_, 1);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v_decl_1349_, 0);
lean_dec(v_unused_1399_);
v___x_1380_ = v_decl_1349_;
v_isShared_1381_ = v_isSharedCheck_1395_;
goto v_resetjp_1379_;
}
else
{
lean_dec(v_decl_1349_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1395_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_value_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1394_; 
v_value_1382_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1384_ = v___x_1378_;
v_isShared_1385_ = v_isSharedCheck_1394_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_value_1382_);
lean_dec(v___x_1378_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1394_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1386_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_value_1382_);
if (v_isShared_1385_ == 0)
{
v___x_1388_ = v___x_1384_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_value_1382_);
v___x_1388_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1390_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 3, v___x_1388_);
lean_ctor_set(v___x_1380_, 2, v___x_1386_);
v___x_1390_ = v___x_1380_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_fvarId_1365_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_binderName_1366_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; 
v___x_1391_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1350_, v___x_1390_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1391_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1400_; 
lean_inc(v_fvarId_1365_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_decl_1349_);
v___x_1400_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1350_, v_fvarId_1365_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1400_;
}
case 2:
{
lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1500_; 
lean_inc(v_binderName_1366_);
lean_inc(v_fvarId_1365_);
lean_del_object(v___x_1376_);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_decl_1349_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; lean_object* v_unused_1504_; 
v_unused_1501_ = lean_ctor_get(v_decl_1349_, 3);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_decl_1349_, 2);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_decl_1349_, 1);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_decl_1349_, 0);
lean_dec(v_unused_1504_);
v___x_1402_ = v_decl_1349_;
v_isShared_1403_ = v_isSharedCheck_1500_;
goto v_resetjp_1401_;
}
else
{
lean_dec(v_decl_1349_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1500_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v_typeName_1404_; lean_object* v_idx_1405_; lean_object* v_struct_1406_; lean_object* v___x_1407_; 
v_typeName_1404_ = lean_ctor_get(v___x_1378_, 0);
lean_inc_n(v_typeName_1404_, 2);
v_idx_1405_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_idx_1405_);
v_struct_1406_ = lean_ctor_get(v___x_1378_, 2);
lean_inc(v_struct_1406_);
lean_dec_ref_known(v___x_1378_, 3);
v___x_1407_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_1404_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
if (lean_obj_tag(v_a_1408_) == 1)
{
lean_object* v_val_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_typeName_1404_);
lean_del_object(v___x_1402_);
lean_dec(v_binderName_1366_);
v_val_1409_ = lean_ctor_get(v_a_1408_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_a_1408_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1411_ = v_a_1408_;
v_isShared_1412_ = v_isSharedCheck_1444_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_val_1409_);
lean_dec(v_a_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1444_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v_fieldIdx_1413_; uint8_t v___x_1414_; 
v_fieldIdx_1413_ = lean_ctor_get(v_val_1409_, 2);
lean_inc(v_fieldIdx_1413_);
lean_dec(v_val_1409_);
v___x_1414_ = lean_nat_dec_eq(v_fieldIdx_1413_, v_idx_1405_);
lean_dec(v_idx_1405_);
lean_dec(v_fieldIdx_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v_subst_1416_; lean_object* v_jpParamMask_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1427_; 
lean_del_object(v___x_1411_);
lean_dec(v_struct_1406_);
v___x_1415_ = lean_st_ref_take(v_a_1351_);
v_subst_1416_ = lean_ctor_get(v___x_1415_, 0);
v_jpParamMask_1417_ = lean_ctor_get(v___x_1415_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1419_ = v___x_1415_;
v_isShared_1420_ = v_isSharedCheck_1427_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_jpParamMask_1417_);
lean_inc(v_subst_1416_);
lean_dec(v___x_1415_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1427_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1416_, v_fvarId_1365_, v___x_1372_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1421_);
v___x_1423_ = v___x_1419_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_jpParamMask_1417_);
v___x_1423_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_st_ref_put(v_a_1351_, v___x_1423_);
v___x_1425_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1425_;
}
}
}
else
{
lean_object* v___x_1429_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v_struct_1406_);
v___x_1429_ = v___x_1411_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_struct_1406_);
v___x_1429_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v_subst_1431_; lean_object* v_jpParamMask_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1442_; 
v___x_1430_ = lean_st_ref_take(v_a_1351_);
v_subst_1431_ = lean_ctor_get(v___x_1430_, 0);
v_jpParamMask_1432_ = lean_ctor_get(v___x_1430_, 1);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1434_ = v___x_1430_;
v_isShared_1435_ = v_isSharedCheck_1442_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_jpParamMask_1432_);
lean_inc(v_subst_1431_);
lean_dec(v___x_1430_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1442_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1431_, v_fvarId_1365_, v___x_1429_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_jpParamMask_1432_);
v___x_1438_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_st_ref_put(v_a_1351_, v___x_1438_);
v___x_1440_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1440_;
}
}
}
}
}
}
else
{
lean_object* v___x_1445_; lean_object* v_subst_1446_; lean_object* v___x_1447_; 
lean_dec(v_a_1408_);
v___x_1445_ = lean_st_ref_get(v_a_1351_);
v_subst_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc_ref(v_subst_1446_);
lean_dec(v___x_1445_);
v___x_1447_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1446_, v_struct_1406_, v___x_1371_);
lean_dec_ref(v_subst_1446_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_fvarId_1448_; lean_object* v___x_1449_; lean_object* v_env_1450_; uint8_t v___x_1451_; lean_object* v___x_1452_; 
v_fvarId_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_fvarId_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1449_ = lean_st_ref_get(v_a_1355_);
v_env_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc_ref(v_env_1450_);
lean_dec(v___x_1449_);
v___x_1451_ = 0;
v___x_1452_ = l_Lean_Environment_find_x3f(v_env_1450_, v_typeName_1404_, v___x_1451_);
if (lean_obj_tag(v___x_1452_) == 1)
{
lean_object* v_val_1453_; 
v_val_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_val_1453_);
lean_dec_ref_known(v___x_1452_, 1);
if (lean_obj_tag(v_val_1453_) == 5)
{
lean_object* v_val_1454_; lean_object* v_ctors_1455_; 
v_val_1454_ = lean_ctor_get(v_val_1453_, 0);
lean_inc_ref(v_val_1454_);
lean_dec_ref_known(v_val_1453_, 1);
v_ctors_1455_ = lean_ctor_get(v_val_1454_, 4);
lean_inc(v_ctors_1455_);
lean_dec_ref(v_val_1454_);
if (lean_obj_tag(v_ctors_1455_) == 1)
{
lean_object* v_tail_1456_; 
v_tail_1456_ = lean_ctor_get(v_ctors_1455_, 1);
if (lean_obj_tag(v_tail_1456_) == 0)
{
lean_object* v_head_1457_; lean_object* v___x_1458_; 
v_head_1457_ = lean_ctor_get(v_ctors_1455_, 0);
lean_inc(v_head_1457_);
lean_dec_ref_known(v_ctors_1455_, 2);
v___x_1458_ = l_Lean_Compiler_LCNF_getCtorLayout(v_head_1457_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v_ctorInfo_1460_; lean_object* v_fieldInfo_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v_fst_1464_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 1);
v_ctorInfo_1460_ = lean_ctor_get(v_a_1459_, 0);
lean_inc_ref(v_ctorInfo_1460_);
v_fieldInfo_1461_ = lean_ctor_get(v_a_1459_, 1);
lean_inc_ref(v_fieldInfo_1461_);
lean_dec(v_a_1459_);
v___x_1462_ = lean_array_get(v___x_1369_, v_fieldInfo_1461_, v_idx_1405_);
lean_dec(v_idx_1405_);
lean_dec_ref(v_fieldInfo_1461_);
v___x_1463_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_fvarId_1448_, v_ctorInfo_1460_, v___x_1462_);
lean_dec_ref(v_ctorInfo_1460_);
v_fst_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_fst_1464_);
if (lean_obj_tag(v_fst_1464_) == 1)
{
lean_object* v___x_1465_; 
lean_dec_ref(v___x_1463_);
lean_del_object(v___x_1402_);
lean_dec(v_binderName_1366_);
v___x_1465_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1350_, v_fvarId_1365_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1465_;
}
else
{
lean_object* v_snd_1466_; lean_object* v___x_1468_; 
v_snd_1466_ = lean_ctor_get(v___x_1463_, 1);
lean_inc(v_snd_1466_);
lean_dec_ref(v___x_1463_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 3, v_fst_1464_);
lean_ctor_set(v___x_1402_, 2, v_snd_1466_);
v___x_1468_ = v___x_1402_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_fvarId_1365_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_binderName_1366_);
lean_ctor_set(v_reuseFailAlloc_1470_, 2, v_snd_1466_);
lean_ctor_set(v_reuseFailAlloc_1470_, 3, v_fst_1464_);
v___x_1468_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1469_; 
v___x_1469_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1350_, v___x_1468_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1469_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_fvarId_1448_);
lean_dec(v_idx_1405_);
lean_del_object(v___x_1402_);
lean_dec(v_binderName_1366_);
lean_dec(v_fvarId_1365_);
lean_dec_ref(v_k_1350_);
v_a_1471_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1458_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1458_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1455_, 2);
lean_dec(v_fvarId_1448_);
lean_dec(v_idx_1405_);
lean_del_object(v___x_1402_);
lean_dec(v_binderName_1366_);
lean_dec(v_fvarId_1365_);
lean_dec_ref(v_k_1350_);
v___y_1358_ = v_a_1351_;
v___y_1359_ = v_a_1352_;
v___y_1360_ = v_a_1353_;
v___y_1361_ = v_a_1354_;
v___y_1362_ = v_a_1355_;
goto v___jp_1357_;
}
}
else
{
lean_dec(v_ctors_1455_);
lean_dec(v_fvarId_1448_);
lean_dec(v_idx_1405_);
lean_del_object(v___x_1402_);
lean_dec(v_binderName_1366_);
lean_dec(v_fvarId_1365_);
lean_dec_ref(v_k_1350_);
v___y_1358_ = v_a_1351_;
v___y_1359_ = v_a_1352_;
v___y_1360_ = v_a_1353_;
v___y_1361_ = v_a_1354_;
v___y_1362_ = v_a_1355_;
goto v___jp_1357_;
}
}
else
{
lean_dec(v_val_1453_);
lean_dec(v_fvarId_1448_);
lean_dec(v_idx_1405_);
lean_del_object(v___x_1402_);
lean_dec(v_binderName_1366_);
lean_dec(v_fvarId_1365_);
lean_dec_ref(v_k_1350_);
v___y_1358_ = v_a_1351_;
v___y_1359_ = v_a_1352_;
v___y_1360_ = v_a_1353_;
v___y_1361_ = v_a_1354_;
v___y_1362_ = v_a_1355_;
goto v___jp_1357_;
}
}
else
{
lean_dec(v___x_1452_);
lean_dec(v_fvarId_1448_);
lean_dec(v_idx_1405_);
lean_del_object(v___x_1402_);
lean_dec(v_binderName_1366_);
lean_dec(v_fvarId_1365_);
lean_dec_ref(v_k_1350_);
v___y_1358_ = v_a_1351_;
v___y_1359_ = v_a_1352_;
v___y_1360_ = v_a_1353_;
v___y_1361_ = v_a_1354_;
v___y_1362_ = v_a_1355_;
goto v___jp_1357_;
}
}
else
{
lean_object* v___x_1479_; lean_object* v_subst_1480_; lean_object* v_jpParamMask_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v_idx_1405_);
lean_dec(v_typeName_1404_);
lean_del_object(v___x_1402_);
lean_dec(v_binderName_1366_);
v___x_1479_ = lean_st_ref_take(v_a_1351_);
v_subst_1480_ = lean_ctor_get(v___x_1479_, 0);
v_jpParamMask_1481_ = lean_ctor_get(v___x_1479_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1483_ = v___x_1479_;
v_isShared_1484_ = v_isSharedCheck_1491_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_jpParamMask_1481_);
lean_inc(v_subst_1480_);
lean_dec(v___x_1479_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1491_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1485_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1480_, v_fvarId_1365_, v___x_1372_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1485_);
v___x_1487_ = v___x_1483_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_jpParamMask_1481_);
v___x_1487_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_st_ref_put(v_a_1351_, v___x_1487_);
v___x_1489_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1489_;
}
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_struct_1406_);
lean_dec(v_idx_1405_);
lean_dec(v_typeName_1404_);
lean_del_object(v___x_1402_);
lean_dec(v_binderName_1366_);
lean_dec(v_fvarId_1365_);
lean_dec_ref(v_k_1350_);
v_a_1492_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1407_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1407_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
case 3:
{
lean_object* v_declName_1505_; lean_object* v_args_1506_; size_t v_sz_1507_; size_t v___x_1508_; lean_object* v___x_1509_; 
v_declName_1505_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_declName_1505_);
v_args_1506_ = lean_ctor_get(v___x_1378_, 2);
lean_inc_ref_n(v_args_1506_, 2);
lean_dec_ref_known(v___x_1378_, 3);
v_sz_1507_ = lean_array_size(v_args_1506_);
v___x_1508_ = ((size_t)0ULL);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_1507_, v___x_1508_, v_args_1506_, v_a_1351_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1511_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
lean_inc(v_declName_1505_);
v___x_1511_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1505_, v_a_1355_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
if (lean_obj_tag(v_a_1512_) == 1)
{
lean_object* v_val_1513_; lean_object* v_params_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec_ref(v_args_1506_);
lean_del_object(v___x_1376_);
v_val_1513_ = lean_ctor_get(v_a_1512_, 0);
lean_inc(v_val_1513_);
lean_dec_ref_known(v_a_1512_, 1);
v_params_1514_ = lean_ctor_get(v_val_1513_, 3);
lean_inc_ref(v_params_1514_);
lean_dec(v_val_1513_);
v___x_1515_ = lean_array_get_size(v_params_1514_);
lean_dec_ref(v_params_1514_);
v___x_1516_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1349_, v_k_1350_, v_declName_1505_, v___x_1515_, v_a_1510_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1516_;
}
else
{
lean_object* v___x_1517_; 
lean_dec(v_a_1512_);
lean_inc(v_declName_1505_);
v___x_1517_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1505_, v_a_1355_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
if (lean_obj_tag(v_a_1518_) == 1)
{
lean_object* v_val_1519_; lean_object* v_toSignature_1520_; lean_object* v_params_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
lean_dec_ref(v_args_1506_);
lean_del_object(v___x_1376_);
v_val_1519_ = lean_ctor_get(v_a_1518_, 0);
lean_inc(v_val_1519_);
lean_dec_ref_known(v_a_1518_, 1);
v_toSignature_1520_ = lean_ctor_get(v_val_1519_, 0);
lean_inc_ref(v_toSignature_1520_);
lean_dec(v_val_1519_);
v_params_1521_ = lean_ctor_get(v_toSignature_1520_, 3);
lean_inc_ref(v_params_1521_);
lean_dec_ref(v_toSignature_1520_);
v___x_1522_ = lean_array_get_size(v_params_1521_);
lean_dec_ref(v_params_1521_);
v___x_1523_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1349_, v_k_1350_, v_declName_1505_, v___x_1522_, v_a_1510_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1523_;
}
else
{
lean_object* v___x_1524_; lean_object* v_env_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; 
lean_dec(v_a_1518_);
v___x_1524_ = lean_st_ref_get(v_a_1355_);
v_env_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc_ref(v_env_1525_);
lean_dec(v___x_1524_);
v___x_1526_ = 0;
lean_inc(v_declName_1505_);
v___x_1527_ = l_Lean_Environment_find_x3f(v_env_1525_, v_declName_1505_, v___x_1526_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v_a_1510_);
lean_dec_ref(v_args_1506_);
lean_dec(v_declName_1505_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
v___x_1528_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4);
v___x_1529_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1528_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1529_;
}
else
{
lean_object* v_val_1530_; 
v_val_1530_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_val_1530_);
lean_dec_ref_known(v___x_1527_, 1);
switch(lean_obj_tag(v_val_1530_))
{
case 0:
{
lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v_a_1510_);
lean_dec_ref(v_args_1506_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_val_1530_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v_val_1530_, 0);
lean_dec(v_unused_1547_);
v___x_1532_ = v_val_1530_;
v_isShared_1533_ = v_isSharedCheck_1546_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v_val_1530_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1546_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1534_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1535_ = l_Lean_Name_toString(v_declName_1505_, v___x_1371_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 3);
lean_ctor_set(v___x_1532_, 0, v___x_1535_);
v___x_1537_ = v___x_1532_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1539_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 5);
lean_ctor_set(v___x_1376_, 1, v___x_1537_);
lean_ctor_set(v___x_1376_, 0, v___x_1534_);
v___x_1539_ = v___x_1376_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1540_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = l_Lean_MessageData_ofFormat(v___x_1541_);
v___x_1543_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1542_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1543_;
}
}
}
}
case 2:
{
lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_a_1510_);
lean_dec_ref(v_args_1506_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_val_1530_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; 
v_unused_1564_ = lean_ctor_get(v_val_1530_, 0);
lean_dec(v_unused_1564_);
v___x_1549_ = v_val_1530_;
v_isShared_1550_ = v_isSharedCheck_1563_;
goto v_resetjp_1548_;
}
else
{
lean_dec(v_val_1530_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1563_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1551_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1552_ = l_Lean_Name_toString(v_declName_1505_, v___x_1371_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set_tag(v___x_1549_, 3);
lean_ctor_set(v___x_1549_, 0, v___x_1552_);
v___x_1554_ = v___x_1549_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 5);
lean_ctor_set(v___x_1376_, 1, v___x_1554_);
lean_ctor_set(v___x_1376_, 0, v___x_1551_);
v___x_1556_ = v___x_1376_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1557_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = l_Lean_MessageData_ofFormat(v___x_1558_);
v___x_1560_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1559_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1560_;
}
}
}
}
case 4:
{
lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1580_; 
lean_dec(v_a_1510_);
lean_dec_ref(v_args_1506_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_val_1530_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v_val_1530_, 0);
lean_dec(v_unused_1581_);
v___x_1566_ = v_val_1530_;
v_isShared_1567_ = v_isSharedCheck_1580_;
goto v_resetjp_1565_;
}
else
{
lean_dec(v_val_1530_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1580_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1568_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1569_ = l_Lean_Name_toString(v_declName_1505_, v___x_1371_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set_tag(v___x_1566_, 3);
lean_ctor_set(v___x_1566_, 0, v___x_1569_);
v___x_1571_ = v___x_1566_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1573_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 5);
lean_ctor_set(v___x_1376_, 1, v___x_1571_);
lean_ctor_set(v___x_1376_, 0, v___x_1568_);
v___x_1573_ = v___x_1376_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1574_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = l_Lean_MessageData_ofFormat(v___x_1575_);
v___x_1577_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1576_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1577_;
}
}
}
}
case 5:
{
lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v_a_1510_);
lean_dec_ref(v_args_1506_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_val_1530_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v_val_1530_, 0);
lean_dec(v_unused_1598_);
v___x_1583_ = v_val_1530_;
v_isShared_1584_ = v_isSharedCheck_1597_;
goto v_resetjp_1582_;
}
else
{
lean_dec(v_val_1530_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1597_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1585_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1586_ = l_Lean_Name_toString(v_declName_1505_, v___x_1371_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set_tag(v___x_1583_, 3);
lean_ctor_set(v___x_1583_, 0, v___x_1586_);
v___x_1588_ = v___x_1583_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1590_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 5);
lean_ctor_set(v___x_1376_, 1, v___x_1588_);
lean_ctor_set(v___x_1376_, 0, v___x_1585_);
v___x_1590_ = v___x_1376_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1591_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = l_Lean_MessageData_ofFormat(v___x_1592_);
v___x_1594_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1593_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1594_;
}
}
}
}
case 6:
{
lean_object* v_val_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1733_; 
v_val_1599_ = lean_ctor_get(v_val_1530_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_val_1530_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1601_ = v_val_1530_;
v_isShared_1602_ = v_isSharedCheck_1733_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_val_1599_);
lean_dec(v_val_1530_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1733_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v_induct_1603_; lean_object* v_cidx_1604_; lean_object* v_numParams_1605_; lean_object* v___x_1606_; 
v_induct_1603_ = lean_ctor_get(v_val_1599_, 1);
lean_inc_n(v_induct_1603_, 2);
v_cidx_1604_ = lean_ctor_get(v_val_1599_, 2);
lean_inc(v_cidx_1604_);
v_numParams_1605_ = lean_ctor_get(v_val_1599_, 3);
lean_inc(v_numParams_1605_);
lean_dec_ref(v_val_1599_);
v___x_1606_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_induct_1603_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1606_, 1);
if (lean_obj_tag(v_a_1607_) == 1)
{
lean_object* v_val_1608_; lean_object* v_numParams_1609_; lean_object* v_fieldIdx_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v_subst_1614_; lean_object* v_jpParamMask_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1625_; 
lean_inc(v_fvarId_1365_);
lean_dec(v_numParams_1605_);
lean_dec(v_cidx_1604_);
lean_dec(v_induct_1603_);
lean_del_object(v___x_1601_);
lean_dec(v_a_1510_);
lean_dec(v_declName_1505_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_decl_1349_);
v_val_1608_ = lean_ctor_get(v_a_1607_, 0);
lean_inc(v_val_1608_);
lean_dec_ref_known(v_a_1607_, 1);
v_numParams_1609_ = lean_ctor_get(v_val_1608_, 1);
lean_inc(v_numParams_1609_);
v_fieldIdx_1610_ = lean_ctor_get(v_val_1608_, 2);
lean_inc(v_fieldIdx_1610_);
lean_dec(v_val_1608_);
v___x_1611_ = lean_nat_add(v_numParams_1609_, v_fieldIdx_1610_);
lean_dec(v_fieldIdx_1610_);
lean_dec(v_numParams_1609_);
v___x_1612_ = lean_array_get(v___x_1372_, v_args_1506_, v___x_1611_);
lean_dec(v___x_1611_);
lean_dec_ref(v_args_1506_);
v___x_1613_ = lean_st_ref_take(v_a_1351_);
v_subst_1614_ = lean_ctor_get(v___x_1613_, 0);
v_jpParamMask_1615_ = lean_ctor_get(v___x_1613_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1617_ = v___x_1613_;
v_isShared_1618_ = v_isSharedCheck_1625_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_jpParamMask_1615_);
lean_inc(v_subst_1614_);
lean_dec(v___x_1613_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1625_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1614_, v_fvarId_1365_, v___x_1612_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1619_);
v___x_1621_ = v___x_1617_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_jpParamMask_1615_);
v___x_1621_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_st_ref_put(v_a_1351_, v___x_1621_);
v___x_1623_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1623_;
}
}
}
else
{
lean_object* v___x_1626_; 
lean_dec(v_a_1607_);
lean_dec_ref(v_args_1506_);
v___x_1626_ = l_Lean_Compiler_LCNF_nameToImpureType(v_induct_1603_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; uint8_t v___x_1628_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1628_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; 
lean_dec(v_a_1627_);
lean_dec(v_cidx_1604_);
lean_del_object(v___x_1601_);
v___x_1629_ = l_Lean_Compiler_LCNF_getCtorLayout(v_declName_1505_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1692_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1692_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1692_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v_ctorInfo_1639_; lean_object* v_fieldInfo_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1691_; 
v_ctorInfo_1639_ = lean_ctor_get(v_a_1630_, 0);
v_fieldInfo_1640_ = lean_ctor_get(v_a_1630_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_a_1630_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1642_ = v_a_1630_;
v_isShared_1643_ = v_isSharedCheck_1691_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_fieldInfo_1640_);
lean_inc(v_ctorInfo_1639_);
lean_dec(v_a_1630_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1691_;
goto v_resetjp_1641_;
}
v___jp_1634_:
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1635_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1635_);
v___x_1637_ = v___x_1632_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1644_ = lean_array_get_size(v_a_1510_);
v___x_1645_ = l_Array_extract___redArg(v_a_1510_, v_numParams_1605_, v___x_1644_);
lean_dec(v_a_1510_);
v___x_1646_ = lean_array_get_size(v___x_1645_);
v___x_1647_ = lean_array_get_size(v_fieldInfo_1640_);
v___x_1648_ = lean_nat_dec_eq(v___x_1646_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_dec_ref(v___x_1645_);
lean_del_object(v___x_1642_);
lean_dec_ref(v_fieldInfo_1640_);
lean_dec_ref(v_ctorInfo_1639_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
goto v___jp_1634_;
}
else
{
if (v___x_1628_ == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_del_object(v___x_1632_);
v___x_1649_ = lean_unsigned_to_nat(0u);
v___x_1650_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_1651_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1647_, v_fieldInfo_1640_, v___x_1645_, v___x_1649_, v___x_1650_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1653_ = 1;
v___x_1654_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_ctorInfo_1639_);
lean_inc_ref(v_ctorInfo_1639_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 5);
lean_ctor_set(v___x_1642_, 1, v_a_1652_);
v___x_1656_ = v___x_1642_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_ctorInfo_1639_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_a_1652_);
v___x_1656_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v_lctx_1659_; lean_object* v_nextIdx_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1681_; 
lean_inc(v_binderName_1366_);
lean_inc(v_fvarId_1365_);
v___x_1657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1657_, 0, v_fvarId_1365_);
lean_ctor_set(v___x_1657_, 1, v_binderName_1366_);
lean_ctor_set(v___x_1657_, 2, v___x_1654_);
lean_ctor_set(v___x_1657_, 3, v___x_1656_);
v___x_1658_ = lean_st_ref_take(v_a_1353_);
v_lctx_1659_ = lean_ctor_get(v___x_1658_, 0);
v_nextIdx_1660_ = lean_ctor_get(v___x_1658_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1662_ = v___x_1658_;
v_isShared_1663_ = v_isSharedCheck_1681_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_nextIdx_1660_);
lean_inc(v_lctx_1659_);
lean_dec(v___x_1658_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1681_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
lean_inc_ref(v___x_1657_);
v___x_1664_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1653_, v_lctx_1659_, v___x_1657_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1664_);
v___x_1666_ = v___x_1662_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_nextIdx_1660_);
v___x_1666_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_st_ref_put(v_a_1353_, v___x_1666_);
v___x_1668_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_1349_, v_k_1350_, v_ctorInfo_1639_, v_fieldInfo_1640_, v___x_1645_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
lean_dec_ref(v___x_1645_);
lean_dec_ref(v_fieldInfo_1640_);
lean_dec_ref(v_ctorInfo_1639_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1679_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1679_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1679_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 1, v_a_1669_);
lean_ctor_set(v___x_1376_, 0, v___x_1657_);
v___x_1674_ = v___x_1376_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1676_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1674_);
v___x_1676_ = v___x_1671_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1657_, 4);
lean_del_object(v___x_1376_);
return v___x_1668_;
}
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref(v___x_1645_);
lean_del_object(v___x_1642_);
lean_dec_ref(v_fieldInfo_1640_);
lean_dec_ref(v_ctorInfo_1639_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
v_a_1683_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1651_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1651_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
else
{
lean_dec_ref(v___x_1645_);
lean_del_object(v___x_1642_);
lean_dec_ref(v_fieldInfo_1640_);
lean_dec_ref(v_ctorInfo_1639_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
goto v___jp_1634_;
}
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec(v_numParams_1605_);
lean_dec(v_a_1510_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
v_a_1693_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1629_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1629_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1712_; 
lean_inc(v_binderName_1366_);
lean_inc(v_fvarId_1365_);
lean_dec(v_numParams_1605_);
lean_dec(v_a_1510_);
lean_dec(v_declName_1505_);
lean_del_object(v___x_1376_);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_decl_1349_);
if (v_isSharedCheck_1712_ == 0)
{
lean_object* v_unused_1713_; lean_object* v_unused_1714_; lean_object* v_unused_1715_; lean_object* v_unused_1716_; 
v_unused_1713_ = lean_ctor_get(v_decl_1349_, 3);
lean_dec(v_unused_1713_);
v_unused_1714_ = lean_ctor_get(v_decl_1349_, 2);
lean_dec(v_unused_1714_);
v_unused_1715_ = lean_ctor_get(v_decl_1349_, 1);
lean_dec(v_unused_1715_);
v_unused_1716_ = lean_ctor_get(v_decl_1349_, 0);
lean_dec(v_unused_1716_);
v___x_1702_ = v_decl_1349_;
v_isShared_1703_ = v_isSharedCheck_1712_;
goto v_resetjp_1701_;
}
else
{
lean_dec(v_decl_1349_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1712_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1704_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_1627_, v_cidx_1604_);
lean_dec(v_cidx_1604_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set_tag(v___x_1601_, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1704_);
v___x_1706_ = v___x_1601_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1708_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 3, v___x_1706_);
lean_ctor_set(v___x_1702_, 2, v_a_1627_);
v___x_1708_ = v___x_1702_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_fvarId_1365_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_binderName_1366_);
lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_a_1627_);
lean_ctor_set(v_reuseFailAlloc_1710_, 3, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1709_; 
v___x_1709_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1350_, v___x_1708_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1709_;
}
}
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec(v_numParams_1605_);
lean_dec(v_cidx_1604_);
lean_del_object(v___x_1601_);
lean_dec(v_a_1510_);
lean_dec(v_declName_1505_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
v_a_1717_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1626_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1626_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec(v_numParams_1605_);
lean_dec(v_cidx_1604_);
lean_dec(v_induct_1603_);
lean_del_object(v___x_1601_);
lean_dec(v_a_1510_);
lean_dec_ref(v_args_1506_);
lean_dec(v_declName_1505_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
v_a_1725_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1606_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1606_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
case 7:
{
lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1749_; 
lean_dec(v_a_1510_);
lean_dec_ref(v_args_1506_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_val_1530_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v_val_1530_, 0);
lean_dec(v_unused_1750_);
v___x_1735_ = v_val_1530_;
v_isShared_1736_ = v_isSharedCheck_1749_;
goto v_resetjp_1734_;
}
else
{
lean_dec(v_val_1530_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1749_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11));
v___x_1738_ = l_Lean_Name_toString(v_declName_1505_, v___x_1371_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 3);
lean_ctor_set(v___x_1735_, 0, v___x_1738_);
v___x_1740_ = v___x_1735_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1742_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 5);
lean_ctor_set(v___x_1376_, 1, v___x_1740_);
lean_ctor_set(v___x_1376_, 0, v___x_1737_);
v___x_1742_ = v___x_1376_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1743_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13));
v___x_1744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1742_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = l_Lean_MessageData_ofFormat(v___x_1744_);
v___x_1746_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1745_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1746_;
}
}
}
}
default: 
{
lean_object* v___x_1751_; 
lean_dec(v_val_1530_);
lean_dec_ref(v_args_1506_);
lean_del_object(v___x_1376_);
v___x_1751_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1349_, v_k_1350_, v_declName_1505_, v_a_1510_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1751_;
}
}
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec(v_a_1510_);
lean_dec_ref(v_args_1506_);
lean_dec(v_declName_1505_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
v_a_1752_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1517_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1517_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec(v_a_1510_);
lean_dec_ref(v_args_1506_);
lean_dec(v_declName_1505_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
v_a_1760_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1511_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1511_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v_args_1506_);
lean_dec(v_declName_1505_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_decl_1349_);
v_a_1768_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1509_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1509_);
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
default: 
{
lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1815_; 
lean_inc_ref(v_type_1367_);
lean_inc(v_binderName_1366_);
lean_inc(v_fvarId_1365_);
lean_del_object(v___x_1376_);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_decl_1349_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; lean_object* v_unused_1817_; lean_object* v_unused_1818_; lean_object* v_unused_1819_; 
v_unused_1816_ = lean_ctor_get(v_decl_1349_, 3);
lean_dec(v_unused_1816_);
v_unused_1817_ = lean_ctor_get(v_decl_1349_, 2);
lean_dec(v_unused_1817_);
v_unused_1818_ = lean_ctor_get(v_decl_1349_, 1);
lean_dec(v_unused_1818_);
v_unused_1819_ = lean_ctor_get(v_decl_1349_, 0);
lean_dec(v_unused_1819_);
v___x_1777_ = v_decl_1349_;
v_isShared_1778_ = v_isSharedCheck_1815_;
goto v_resetjp_1776_;
}
else
{
lean_dec(v_decl_1349_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1815_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_fvarId_1779_; lean_object* v_args_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1814_; 
v_fvarId_1779_ = lean_ctor_get(v___x_1378_, 0);
v_args_1780_ = lean_ctor_get(v___x_1378_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1782_ = v___x_1378_;
v_isShared_1783_ = v_isSharedCheck_1814_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_args_1780_);
lean_inc(v_fvarId_1779_);
lean_dec(v___x_1378_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1814_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
size_t v_sz_1784_; size_t v___x_1785_; lean_object* v___x_1786_; 
v_sz_1784_ = lean_array_size(v_args_1780_);
v___x_1785_ = ((size_t)0ULL);
v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_1784_, v___x_1785_, v_args_1780_, v_a_1351_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1788_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
v___x_1788_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1367_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1789_);
lean_dec(v_a_1789_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 1, v_a_1787_);
v___x_1792_ = v___x_1782_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_fvarId_1779_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1794_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 3, v___x_1792_);
lean_ctor_set(v___x_1777_, 2, v___x_1790_);
v___x_1794_ = v___x_1777_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_fvarId_1365_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_binderName_1366_);
lean_ctor_set(v_reuseFailAlloc_1796_, 2, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1796_, 3, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; 
v___x_1795_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1350_, v___x_1794_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1795_;
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_a_1787_);
lean_del_object(v___x_1782_);
lean_dec(v_fvarId_1779_);
lean_del_object(v___x_1777_);
lean_dec(v_binderName_1366_);
lean_dec(v_fvarId_1365_);
lean_dec_ref(v_k_1350_);
v_a_1798_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1788_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1788_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_del_object(v___x_1782_);
lean_dec(v_fvarId_1779_);
lean_del_object(v___x_1777_);
lean_dec_ref(v_type_1367_);
lean_dec(v_binderName_1366_);
lean_dec(v_fvarId_1365_);
lean_dec_ref(v_k_1350_);
v_a_1806_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1786_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1786_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
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
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1349_ = stack[0].m_obj;
lean_object* v_k_1350_ = stack[1].m_obj;
lean_object* v_a_1351_ = stack[2].m_obj;
lean_object* v_a_1352_ = stack[3].m_obj;
lean_object* v_a_1353_ = stack[4].m_obj;
lean_object* v_a_1354_ = stack[5].m_obj;
lean_object* v_a_1355_ = stack[6].m_obj;
lean_object* v_res_1822_;
v_res_1822_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_1349_, v_k_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
stack->m_obj
 = v_res_1822_;
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1825_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1));
v___x_1826_ = lean_unsigned_to_nat(15u);
v___x_1827_ = lean_unsigned_to_nat(272u);
v___x_1828_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1829_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1830_ = l_mkPanicMessageWithDecl(v___x_1829_, v___x_1828_, v___x_1827_, v___x_1826_, v___x_1825_);
return v___x_1830_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5(void){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_1833_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1835_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6));
v___x_1836_ = lean_unsigned_to_nat(6u);
v___x_1837_ = lean_unsigned_to_nat(251u);
v___x_1838_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1839_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1840_ = l_mkPanicMessageWithDecl(v___x_1839_, v___x_1838_, v___x_1837_, v___x_1836_, v___x_1835_);
return v___x_1840_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1842_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8));
v___x_1843_ = lean_unsigned_to_nat(6u);
v___x_1844_ = lean_unsigned_to_nat(253u);
v___x_1845_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1846_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1847_ = l_mkPanicMessageWithDecl(v___x_1846_, v___x_1845_, v___x_1844_, v___x_1843_, v___x_1842_);
return v___x_1847_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1849_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10));
v___x_1850_ = lean_unsigned_to_nat(6u);
v___x_1851_ = lean_unsigned_to_nat(254u);
v___x_1852_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1853_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1854_ = l_mkPanicMessageWithDecl(v___x_1853_, v___x_1852_, v___x_1851_, v___x_1850_, v___x_1849_);
return v___x_1854_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1856_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12));
v___x_1857_ = lean_unsigned_to_nat(45u);
v___x_1858_ = lean_unsigned_to_nat(252u);
v___x_1859_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1860_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1861_ = l_mkPanicMessageWithDecl(v___x_1860_, v___x_1859_, v___x_1858_, v___x_1857_, v___x_1856_);
return v___x_1861_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1864_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1));
v___x_1865_ = lean_unsigned_to_nat(18u);
v___x_1866_ = lean_unsigned_to_nat(293u);
v___x_1867_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0));
v___x_1868_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1869_ = l_mkPanicMessageWithDecl(v___x_1868_, v___x_1867_, v___x_1866_, v___x_1865_, v___x_1864_);
return v___x_1869_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object* v_discr_1870_, lean_object* v_k_1871_, lean_object* v_ctorInfo_1872_, lean_object* v_params_1873_, lean_object* v_fields_1874_, lean_object* v_i_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = lean_array_get_size(v_params_1873_);
v___x_1891_ = lean_nat_dec_lt(v_i_1875_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; uint8_t v___x_1893_; 
lean_dec(v_discr_1870_);
v___x_1892_ = lean_array_get_size(v_fields_1874_);
v___x_1893_ = lean_nat_dec_lt(v_i_1875_, v___x_1892_);
lean_dec(v_i_1875_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; 
v___x_1894_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1871_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v___x_1894_;
}
else
{
lean_dec_ref(v_k_1871_);
v___y_1883_ = v_a_1876_;
v___y_1884_ = v_a_1877_;
v___y_1885_ = v_a_1878_;
v___y_1886_ = v_a_1879_;
v___y_1887_ = v_a_1880_;
goto v___jp_1882_;
}
}
else
{
lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = lean_array_get_size(v_fields_1874_);
v___x_1896_ = lean_nat_dec_lt(v_i_1875_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_dec(v_i_1875_);
lean_dec_ref(v_k_1871_);
lean_dec(v_discr_1870_);
v___y_1883_ = v_a_1876_;
v___y_1884_ = v_a_1877_;
v___y_1885_ = v_a_1878_;
v___y_1886_ = v_a_1879_;
v___y_1887_ = v_a_1880_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v_fst_1899_; lean_object* v_snd_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1952_; 
v___x_1897_ = lean_array_fget_borrowed(v_fields_1874_, v_i_1875_);
lean_inc(v___x_1897_);
lean_inc(v_discr_1870_);
v___x_1898_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_discr_1870_, v_ctorInfo_1872_, v___x_1897_);
v_fst_1899_ = lean_ctor_get(v___x_1898_, 0);
v_snd_1900_ = lean_ctor_get(v___x_1898_, 1);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1902_ = v___x_1898_;
v_isShared_1903_ = v_isSharedCheck_1952_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_snd_1900_);
lean_inc(v_fst_1899_);
lean_dec(v___x_1898_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1952_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_array_fget_borrowed(v_params_1873_, v_i_1875_);
if (lean_obj_tag(v_fst_1899_) == 1)
{
lean_object* v_fvarId_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_subst_1908_; lean_object* v_jpParamMask_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1921_; 
lean_del_object(v___x_1902_);
lean_dec(v_snd_1900_);
v_fvarId_1905_ = lean_ctor_get(v___x_1904_, 0);
v___x_1906_ = lean_box(0);
v___x_1907_ = lean_st_ref_take(v_a_1876_);
v_subst_1908_ = lean_ctor_get(v___x_1907_, 0);
v_jpParamMask_1909_ = lean_ctor_get(v___x_1907_, 1);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1911_ = v___x_1907_;
v_isShared_1912_ = v_isSharedCheck_1921_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_jpParamMask_1909_);
lean_inc(v_subst_1908_);
lean_dec(v___x_1907_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1921_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_inc(v_fvarId_1905_);
v___x_1913_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1908_, v_fvarId_1905_, v___x_1906_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1913_);
v___x_1915_ = v___x_1911_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_jpParamMask_1909_);
v___x_1915_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = lean_st_ref_put(v_a_1876_, v___x_1915_);
v___x_1917_ = lean_unsigned_to_nat(1u);
v___x_1918_ = lean_nat_add(v_i_1875_, v___x_1917_);
lean_dec(v_i_1875_);
v_i_1875_ = v___x_1918_;
goto _start;
}
}
}
else
{
lean_object* v_fvarId_1922_; lean_object* v_binderName_1923_; uint8_t v___x_1924_; lean_object* v_decl_1925_; lean_object* v___x_1926_; lean_object* v_lctx_1927_; lean_object* v_nextIdx_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1951_; 
v_fvarId_1922_ = lean_ctor_get(v___x_1904_, 0);
v_binderName_1923_ = lean_ctor_get(v___x_1904_, 1);
v___x_1924_ = 1;
lean_inc(v_binderName_1923_);
lean_inc(v_fvarId_1922_);
v_decl_1925_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_1925_, 0, v_fvarId_1922_);
lean_ctor_set(v_decl_1925_, 1, v_binderName_1923_);
lean_ctor_set(v_decl_1925_, 2, v_snd_1900_);
lean_ctor_set(v_decl_1925_, 3, v_fst_1899_);
v___x_1926_ = lean_st_ref_take(v_a_1878_);
v_lctx_1927_ = lean_ctor_get(v___x_1926_, 0);
v_nextIdx_1928_ = lean_ctor_get(v___x_1926_, 1);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1930_ = v___x_1926_;
v_isShared_1931_ = v_isSharedCheck_1951_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_nextIdx_1928_);
lean_inc(v_lctx_1927_);
lean_dec(v___x_1926_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1951_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
lean_inc_ref(v_decl_1925_);
v___x_1932_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1924_, v_lctx_1927_, v_decl_1925_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1932_);
v___x_1934_ = v___x_1930_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_nextIdx_1928_);
v___x_1934_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1935_ = lean_st_ref_put(v_a_1878_, v___x_1934_);
v___x_1936_ = lean_unsigned_to_nat(1u);
v___x_1937_ = lean_nat_add(v_i_1875_, v___x_1936_);
lean_dec(v_i_1875_);
v___x_1938_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_1870_, v_k_1871_, v_ctorInfo_1872_, v_params_1873_, v_fields_1874_, v___x_1937_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1949_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1949_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1949_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v_a_1939_);
lean_ctor_set(v___x_1902_, 0, v_decl_1925_);
v___x_1944_ = v___x_1902_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_decl_1925_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1944_);
v___x_1946_ = v___x_1941_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_dec_ref_known(v_decl_1925_, 4);
lean_del_object(v___x_1902_);
return v___x_1938_;
}
}
}
}
}
}
}
v___jp_1882_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2);
v___x_1889_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1888_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
return v___x_1889_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_1870_ = stack[0].m_obj;
lean_object* v_k_1871_ = stack[1].m_obj;
lean_object* v_ctorInfo_1872_ = stack[2].m_obj;
lean_object* v_params_1873_ = stack[3].m_obj;
lean_object* v_fields_1874_ = stack[4].m_obj;
lean_object* v_i_1875_ = stack[5].m_obj;
lean_object* v_a_1876_ = stack[6].m_obj;
lean_object* v_a_1877_ = stack[7].m_obj;
lean_object* v_a_1878_ = stack[8].m_obj;
lean_object* v_a_1879_ = stack[9].m_obj;
lean_object* v_a_1880_ = stack[10].m_obj;
lean_object* v_res_1953_;
v_res_1953_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_1870_, v_k_1871_, v_ctorInfo_1872_, v_params_1873_, v_fields_1874_, v_i_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
stack->m_obj
 = v_res_1953_;
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(lean_object* v_discr_1954_, lean_object* v_alt_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
if (lean_obj_tag(v_alt_1955_) == 0)
{
lean_object* v_ctorName_1962_; lean_object* v_params_1963_; lean_object* v_code_1964_; lean_object* v___x_1965_; 
v_ctorName_1962_ = lean_ctor_get(v_alt_1955_, 0);
lean_inc(v_ctorName_1962_);
v_params_1963_ = lean_ctor_get(v_alt_1955_, 1);
lean_inc_ref(v_params_1963_);
v_code_1964_ = lean_ctor_get(v_alt_1955_, 2);
lean_inc_ref(v_code_1964_);
lean_dec_ref_known(v_alt_1955_, 3);
v___x_1965_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_1962_, v_a_1959_, v_a_1960_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v_ctorInfo_1967_; lean_object* v_fieldInfo_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1993_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1965_, 1);
v_ctorInfo_1967_ = lean_ctor_get(v_a_1966_, 0);
v_fieldInfo_1968_ = lean_ctor_get(v_a_1966_, 1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_a_1966_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1970_ = v_a_1966_;
v_isShared_1971_ = v_isSharedCheck_1993_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_fieldInfo_1968_);
lean_inc(v_ctorInfo_1967_);
lean_dec(v_a_1966_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1993_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = lean_unsigned_to_nat(0u);
v___x_1973_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_1954_, v_code_1964_, v_ctorInfo_1967_, v_params_1963_, v_fieldInfo_1968_, v___x_1972_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
lean_dec_ref(v_fieldInfo_1968_);
lean_dec_ref(v_params_1963_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1984_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1984_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1984_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set_tag(v___x_1970_, 1);
lean_ctor_set(v___x_1970_, 1, v_a_1974_);
v___x_1979_ = v___x_1970_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_ctorInfo_1967_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1979_);
v___x_1981_ = v___x_1976_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_del_object(v___x_1970_);
lean_dec_ref(v_ctorInfo_1967_);
v_a_1985_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1973_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1973_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v_code_1964_);
lean_dec_ref(v_params_1963_);
lean_dec(v_discr_1954_);
v_a_1994_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1965_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1965_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
else
{
lean_object* v_code_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2026_; 
lean_dec(v_discr_1954_);
v_code_2002_ = lean_ctor_get(v_alt_1955_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_alt_1955_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2004_ = v_alt_1955_;
v_isShared_2005_ = v_isSharedCheck_2026_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_code_2002_);
lean_dec(v_alt_1955_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2026_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; 
v___x_2006_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_2002_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2017_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2017_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2017_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v_a_2007_);
v___x_2012_ = v___x_2004_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2014_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2012_);
v___x_2014_ = v___x_2009_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_del_object(v___x_2004_);
v_a_2018_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2006_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2006_);
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
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_1954_ = stack[0].m_obj;
lean_object* v_alt_1955_ = stack[1].m_obj;
lean_object* v_a_1956_ = stack[2].m_obj;
lean_object* v_a_1957_ = stack[3].m_obj;
lean_object* v_a_1958_ = stack[4].m_obj;
lean_object* v_a_1959_ = stack[5].m_obj;
lean_object* v_a_1960_ = stack[6].m_obj;
lean_object* v_res_2027_;
v_res_2027_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_discr_1954_, v_alt_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
stack->m_obj
 = v_res_2027_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(lean_object* v_fvarId_2028_, size_t v_sz_2029_, size_t v_i_2030_, lean_object* v_bs_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
uint8_t v___x_2038_; 
v___x_2038_ = lean_usize_dec_lt(v_i_2030_, v_sz_2029_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
lean_dec(v_fvarId_2028_);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v_bs_2031_);
return v___x_2039_;
}
else
{
lean_object* v_v_2040_; lean_object* v___x_2041_; lean_object* v_bs_x27_2042_; lean_object* v___x_2043_; 
v_v_2040_ = lean_array_uget(v_bs_2031_, v_i_2030_);
v___x_2041_ = lean_unsigned_to_nat(0u);
v_bs_x27_2042_ = lean_array_uset(v_bs_2031_, v_i_2030_, v___x_2041_);
lean_inc(v_fvarId_2028_);
v___x_2043_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_fvarId_2028_, v_v_2040_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; size_t v___x_2045_; size_t v___x_2046_; lean_object* v___x_2047_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = ((size_t)1ULL);
v___x_2046_ = lean_usize_add(v_i_2030_, v___x_2045_);
v___x_2047_ = lean_array_uset(v_bs_x27_2042_, v_i_2030_, v_a_2044_);
v_i_2030_ = v___x_2046_;
v_bs_2031_ = v___x_2047_;
goto _start;
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec_ref(v_bs_x27_2042_);
lean_dec(v_fvarId_2028_);
v_a_2049_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2043_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2043_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2028_ = stack[0].m_obj;
size_t v_sz_2029_ = stack[1].m_num;
size_t v_i_2030_ = stack[2].m_num;
lean_object* v_bs_2031_ = stack[3].m_obj;
lean_object* v___y_2032_ = stack[4].m_obj;
lean_object* v___y_2033_ = stack[5].m_obj;
lean_object* v___y_2034_ = stack[6].m_obj;
lean_object* v___y_2035_ = stack[7].m_obj;
lean_object* v___y_2036_ = stack[8].m_obj;
lean_object* v_res_2057_;
v_res_2057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2028_, v_sz_2029_, v_i_2030_, v_bs_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
stack->m_obj
 = v_res_2057_;
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(lean_object* v_c_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
switch(lean_obj_tag(v_c_2058_))
{
case 0:
{
lean_object* v_decl_2065_; lean_object* v_k_2066_; lean_object* v___x_2067_; 
v_decl_2065_ = lean_ctor_get(v_c_2058_, 0);
lean_inc_ref(v_decl_2065_);
v_k_2066_ = lean_ctor_get(v_c_2058_, 1);
lean_inc_ref(v_k_2066_);
lean_dec_ref_known(v_c_2058_, 2);
v___x_2067_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2065_, v_k_2066_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
return v___x_2067_;
}
case 1:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec_ref_known(v_c_2058_, 2);
v___x_2068_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2);
v___x_2069_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2068_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
return v___x_2069_;
}
case 2:
{
lean_object* v_decl_2070_; lean_object* v_k_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2163_; 
v_decl_2070_ = lean_ctor_get(v_c_2058_, 0);
v_k_2071_ = lean_ctor_get(v_c_2058_, 1);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_c_2058_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2073_ = v_c_2058_;
v_isShared_2074_ = v_isSharedCheck_2163_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_k_2071_);
lean_inc(v_decl_2070_);
lean_dec(v_c_2058_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2163_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v_fvarId_2075_; lean_object* v_binderName_2076_; lean_object* v_params_2077_; lean_object* v_type_2078_; lean_object* v_value_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2162_; 
v_fvarId_2075_ = lean_ctor_get(v_decl_2070_, 0);
v_binderName_2076_ = lean_ctor_get(v_decl_2070_, 1);
v_params_2077_ = lean_ctor_get(v_decl_2070_, 2);
v_type_2078_ = lean_ctor_get(v_decl_2070_, 3);
v_value_2079_ = lean_ctor_get(v_decl_2070_, 4);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_decl_2070_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2081_ = v_decl_2070_;
v_isShared_2082_ = v_isSharedCheck_2162_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_value_2079_);
lean_inc(v_type_2078_);
lean_inc(v_params_2077_);
lean_inc(v_binderName_2076_);
lean_inc(v_fvarId_2075_);
lean_dec(v_decl_2070_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2162_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
size_t v_sz_2083_; size_t v___x_2084_; lean_object* v___x_2085_; 
v_sz_2083_ = lean_array_size(v_params_2077_);
v___x_2084_ = ((size_t)0ULL);
v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2083_, v___x_2084_, v_params_2077_, v_a_2059_, v_a_2061_, v_a_2062_, v_a_2063_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; size_t v_sz_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v_subst_2090_; lean_object* v_jpParamMask_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2153_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc_n(v_a_2086_, 2);
lean_dec_ref_known(v___x_2085_, 1);
v_sz_2087_ = lean_array_size(v_a_2086_);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_2087_, v___x_2084_, v_a_2086_);
v___x_2089_ = lean_st_ref_take(v_a_2059_);
v_subst_2090_ = lean_ctor_get(v___x_2089_, 0);
v_jpParamMask_2091_ = lean_ctor_get(v___x_2089_, 1);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2093_ = v___x_2089_;
v_isShared_2094_ = v_isSharedCheck_2153_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_jpParamMask_2091_);
lean_inc(v_subst_2090_);
lean_dec(v___x_2089_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2153_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
lean_inc_ref(v___x_2088_);
lean_inc(v_fvarId_2075_);
v___x_2095_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_jpParamMask_2091_, v_fvarId_2075_, v___x_2088_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 1, v___x_2095_);
v___x_2097_ = v___x_2093_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_subst_2090_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; lean_object* v___y_2100_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2098_ = lean_st_ref_put(v_a_2059_, v___x_2097_);
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3));
v___x_2144_ = l_Array_zip___redArg(v_a_2086_, v___x_2088_);
lean_dec_ref(v___x_2088_);
v___x_2145_ = lean_array_get_size(v___x_2144_);
v___x_2146_ = lean_nat_dec_lt(v___x_2142_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_dec_ref(v___x_2144_);
v___y_2100_ = v___x_2143_;
goto v___jp_2099_;
}
else
{
uint8_t v___x_2147_; 
v___x_2147_ = lean_nat_dec_le(v___x_2145_, v___x_2145_);
if (v___x_2147_ == 0)
{
if (v___x_2146_ == 0)
{
lean_dec_ref(v___x_2144_);
v___y_2100_ = v___x_2143_;
goto v___jp_2099_;
}
else
{
size_t v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lean_usize_of_nat(v___x_2145_);
v___x_2149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2144_, v___x_2084_, v___x_2148_, v___x_2143_);
lean_dec_ref(v___x_2144_);
v___y_2100_ = v___x_2149_;
goto v___jp_2099_;
}
}
else
{
size_t v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = lean_usize_of_nat(v___x_2145_);
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2144_, v___x_2084_, v___x_2150_, v___x_2143_);
lean_dec_ref(v___x_2144_);
v___y_2100_ = v___x_2151_;
goto v___jp_2099_;
}
}
v___jp_2099_:
{
lean_object* v___x_2101_; 
v___x_2101_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_value_2079_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2103_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2071_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2103_, 1);
v___x_2105_ = lean_array_get_size(v_a_2086_);
lean_dec(v_a_2086_);
v___x_2106_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2078_, v___x_2105_, v_a_2062_, v_a_2063_);
lean_dec_ref(v_type_2078_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2133_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2133_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2133_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
uint8_t v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = 1;
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 4, v_a_2102_);
lean_ctor_set(v___x_2081_, 3, v_a_2107_);
lean_ctor_set(v___x_2081_, 2, v___y_2100_);
v___x_2113_ = v___x_2081_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_fvarId_2075_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_binderName_2076_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v___y_2100_);
lean_ctor_set(v_reuseFailAlloc_2132_, 3, v_a_2107_);
lean_ctor_set(v_reuseFailAlloc_2132_, 4, v_a_2102_);
v___x_2113_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2114_; lean_object* v_lctx_2115_; lean_object* v_nextIdx_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2131_; 
v___x_2114_ = lean_st_ref_take(v_a_2061_);
v_lctx_2115_ = lean_ctor_get(v___x_2114_, 0);
v_nextIdx_2116_ = lean_ctor_get(v___x_2114_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2118_ = v___x_2114_;
v_isShared_2119_ = v_isSharedCheck_2131_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_nextIdx_2116_);
lean_inc(v_lctx_2115_);
lean_dec(v___x_2114_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2131_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
lean_inc_ref(v___x_2113_);
v___x_2120_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2111_, v_lctx_2115_, v___x_2113_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2120_);
v___x_2122_ = v___x_2118_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_nextIdx_2116_);
v___x_2122_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = lean_st_ref_put(v_a_2061_, v___x_2122_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 1, v_a_2104_);
lean_ctor_set(v___x_2073_, 0, v___x_2113_);
v___x_2125_ = v___x_2073_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_a_2104_);
v___x_2125_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2127_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2125_);
v___x_2127_ = v___x_2109_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_a_2104_);
lean_dec(v_a_2102_);
lean_dec_ref(v___y_2100_);
lean_del_object(v___x_2081_);
lean_dec(v_binderName_2076_);
lean_dec(v_fvarId_2075_);
lean_del_object(v___x_2073_);
v_a_2134_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2106_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2106_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_dec(v_a_2102_);
lean_dec_ref(v___y_2100_);
lean_dec(v_a_2086_);
lean_del_object(v___x_2081_);
lean_dec_ref(v_type_2078_);
lean_dec(v_binderName_2076_);
lean_dec(v_fvarId_2075_);
lean_del_object(v___x_2073_);
return v___x_2103_;
}
}
else
{
lean_dec_ref(v___y_2100_);
lean_dec(v_a_2086_);
lean_del_object(v___x_2081_);
lean_dec_ref(v_type_2078_);
lean_dec(v_binderName_2076_);
lean_dec(v_fvarId_2075_);
lean_del_object(v___x_2073_);
lean_dec_ref(v_k_2071_);
return v___x_2101_;
}
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_del_object(v___x_2081_);
lean_dec_ref(v_value_2079_);
lean_dec_ref(v_type_2078_);
lean_dec(v_binderName_2076_);
lean_dec(v_fvarId_2075_);
lean_del_object(v___x_2073_);
lean_dec_ref(v_k_2071_);
v_a_2154_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2085_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2085_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2164_; lean_object* v_args_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2201_; 
v_fvarId_2164_ = lean_ctor_get(v_c_2058_, 0);
v_args_2165_ = lean_ctor_get(v_c_2058_, 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_c_2058_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2167_ = v_c_2058_;
v_isShared_2168_ = v_isSharedCheck_2201_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_args_2165_);
lean_inc(v_fvarId_2164_);
lean_dec(v_c_2058_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2201_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v_a_2170_; lean_object* v___y_2176_; lean_object* v___x_2186_; lean_object* v_jpParamMask_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2186_ = lean_st_ref_get(v_a_2059_);
v_jpParamMask_2187_ = lean_ctor_get(v___x_2186_, 1);
lean_inc_ref(v_jpParamMask_2187_);
lean_dec(v___x_2186_);
v___x_2188_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_jpParamMask_2187_, v_fvarId_2164_);
lean_dec_ref(v_jpParamMask_2187_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_2191_ = l_Array_zip___redArg(v_args_2165_, v___x_2188_);
lean_dec_ref(v___x_2188_);
lean_dec_ref(v_args_2165_);
v___x_2192_ = lean_array_get_size(v___x_2191_);
v___x_2193_ = lean_nat_dec_lt(v___x_2189_, v___x_2192_);
if (v___x_2193_ == 0)
{
lean_dec_ref(v___x_2191_);
v_a_2170_ = v___x_2190_;
goto v___jp_2169_;
}
else
{
uint8_t v___x_2194_; 
v___x_2194_ = lean_nat_dec_le(v___x_2192_, v___x_2192_);
if (v___x_2194_ == 0)
{
if (v___x_2193_ == 0)
{
lean_dec_ref(v___x_2191_);
v_a_2170_ = v___x_2190_;
goto v___jp_2169_;
}
else
{
size_t v___x_2195_; size_t v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = ((size_t)0ULL);
v___x_2196_ = lean_usize_of_nat(v___x_2192_);
v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2191_, v___x_2195_, v___x_2196_, v___x_2190_, v_a_2059_);
lean_dec_ref(v___x_2191_);
v___y_2176_ = v___x_2197_;
goto v___jp_2175_;
}
}
else
{
size_t v___x_2198_; size_t v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = ((size_t)0ULL);
v___x_2199_ = lean_usize_of_nat(v___x_2192_);
v___x_2200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2191_, v___x_2198_, v___x_2199_, v___x_2190_, v_a_2059_);
lean_dec_ref(v___x_2191_);
v___y_2176_ = v___x_2200_;
goto v___jp_2175_;
}
}
v___jp_2169_:
{
lean_object* v___x_2172_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 1, v_a_2170_);
v___x_2172_ = v___x_2167_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_fvarId_2164_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_a_2170_);
v___x_2172_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
return v___x_2173_;
}
}
v___jp_2175_:
{
if (lean_obj_tag(v___y_2176_) == 0)
{
lean_object* v_a_2177_; 
v_a_2177_ = lean_ctor_get(v___y_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___y_2176_, 1);
v_a_2170_ = v_a_2177_;
goto v___jp_2169_;
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_del_object(v___x_2167_);
lean_dec(v_fvarId_2164_);
v_a_2178_ = lean_ctor_get(v___y_2176_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___y_2176_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___y_2176_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___y_2176_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
}
case 4:
{
lean_object* v_cases_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2312_; 
v_cases_2202_ = lean_ctor_get(v_c_2058_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_c_2058_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2204_ = v_c_2058_;
v_isShared_2205_ = v_isSharedCheck_2312_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_cases_2202_);
lean_dec(v_c_2058_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2312_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_typeName_2206_; lean_object* v_resultType_2207_; lean_object* v_discr_2208_; lean_object* v_alts_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2311_; 
v_typeName_2206_ = lean_ctor_get(v_cases_2202_, 0);
v_resultType_2207_ = lean_ctor_get(v_cases_2202_, 1);
v_discr_2208_ = lean_ctor_get(v_cases_2202_, 2);
v_alts_2209_ = lean_ctor_get(v_cases_2202_, 3);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_cases_2202_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2211_ = v_cases_2202_;
v_isShared_2212_ = v_isSharedCheck_2311_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_alts_2209_);
lean_inc(v_discr_2208_);
lean_inc(v_resultType_2207_);
lean_inc(v_typeName_2206_);
lean_dec(v_cases_2202_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2311_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5);
lean_inc(v_typeName_2206_);
v___x_2214_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_2206_, v_a_2062_, v_a_2063_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
if (lean_obj_tag(v_a_2215_) == 1)
{
lean_object* v_val_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
lean_del_object(v___x_2211_);
lean_dec_ref(v_resultType_2207_);
lean_dec(v_typeName_2206_);
lean_del_object(v___x_2204_);
v_val_2216_ = lean_ctor_get(v_a_2215_, 0);
lean_inc(v_val_2216_);
lean_dec_ref_known(v_a_2215_, 1);
v___x_2217_ = lean_array_get_size(v_alts_2209_);
v___x_2218_ = lean_unsigned_to_nat(1u);
v___x_2219_ = lean_nat_dec_eq(v___x_2217_, v___x_2218_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_dec(v_val_2216_);
lean_dec_ref(v_alts_2209_);
lean_dec(v_discr_2208_);
v___x_2220_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7);
v___x_2221_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2220_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
return v___x_2221_;
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = lean_unsigned_to_nat(0u);
v___x_2223_ = lean_array_get(v___x_2213_, v_alts_2209_, v___x_2222_);
lean_dec_ref(v_alts_2209_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_ctorName_2224_; lean_object* v_params_2225_; lean_object* v_code_2226_; lean_object* v_ctorName_2227_; lean_object* v_fieldIdx_2228_; uint8_t v___x_2229_; 
v_ctorName_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_ctorName_2224_);
v_params_2225_ = lean_ctor_get(v___x_2223_, 1);
lean_inc_ref(v_params_2225_);
v_code_2226_ = lean_ctor_get(v___x_2223_, 2);
lean_inc_ref(v_code_2226_);
lean_dec_ref_known(v___x_2223_, 3);
v_ctorName_2227_ = lean_ctor_get(v_val_2216_, 0);
lean_inc(v_ctorName_2227_);
v_fieldIdx_2228_ = lean_ctor_get(v_val_2216_, 2);
lean_inc(v_fieldIdx_2228_);
lean_dec(v_val_2216_);
v___x_2229_ = lean_name_eq(v_ctorName_2224_, v_ctorName_2227_);
lean_dec(v_ctorName_2227_);
lean_dec(v_ctorName_2224_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v_fieldIdx_2228_);
lean_dec_ref(v_code_2226_);
lean_dec_ref(v_params_2225_);
lean_dec(v_discr_2208_);
v___x_2230_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9);
v___x_2231_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2230_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
return v___x_2231_;
}
else
{
lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2232_ = lean_array_get_size(v_params_2225_);
v___x_2233_ = lean_nat_dec_lt(v_fieldIdx_2228_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
lean_dec(v_fieldIdx_2228_);
lean_dec_ref(v_code_2226_);
lean_dec_ref(v_params_2225_);
lean_dec(v_discr_2208_);
v___x_2234_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11);
v___x_2235_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2234_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
return v___x_2235_;
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = lean_box(0);
v___x_2237_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v___x_2232_, v_params_2225_, v_fieldIdx_2228_, v_discr_2208_, v___x_2222_, v___x_2236_, v_a_2059_);
lean_dec(v_fieldIdx_2228_);
lean_dec_ref(v_params_2225_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_dec_ref_known(v___x_2237_, 1);
v_c_2058_ = v_code_2226_;
goto _start;
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v_code_2226_);
v_a_2239_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2237_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2237_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
lean_dec(v___x_2223_);
lean_dec(v_val_2216_);
lean_dec(v_discr_2208_);
v___x_2247_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13);
v___x_2248_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2247_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
return v___x_2248_;
}
}
}
else
{
uint8_t v___x_2249_; lean_object* v___x_2250_; lean_object* v_subst_2251_; lean_object* v___x_2252_; 
lean_dec(v_a_2215_);
v___x_2249_ = 1;
v___x_2250_ = lean_st_ref_get(v_a_2059_);
v_subst_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc_ref(v_subst_2251_);
lean_dec(v___x_2250_);
v___x_2252_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2251_, v_discr_2208_, v___x_2249_);
lean_dec_ref(v_subst_2251_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_fvarId_2253_; lean_object* v___x_2254_; 
v_fvarId_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_fvarId_2253_);
lean_dec_ref_known(v___x_2252_, 1);
v___x_2254_ = l_Lean_Compiler_LCNF_toImpureType(v_resultType_2207_, v_a_2062_, v_a_2063_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; size_t v_sz_2256_; size_t v___x_2257_; lean_object* v___x_2258_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2254_, 1);
v_sz_2256_ = lean_array_size(v_alts_2209_);
v___x_2257_ = ((size_t)0ULL);
lean_inc(v_fvarId_2253_);
v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2253_, v_sz_2256_, v___x_2257_, v_alts_2209_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2260_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref_known(v___x_2258_, 1);
v___x_2260_ = l_Lean_Compiler_LCNF_nameToImpureType(v_typeName_2206_, v_a_2062_, v_a_2063_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2276_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2263_ = v___x_2260_;
v_isShared_2264_ = v_isSharedCheck_2276_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2276_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2265_ = l_Lean_Expr_getAppFn(v_a_2261_);
lean_dec(v_a_2261_);
v___x_2266_ = l_Lean_Expr_constName_x21(v___x_2265_);
lean_dec_ref(v___x_2265_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 3, v_a_2259_);
lean_ctor_set(v___x_2211_, 2, v_fvarId_2253_);
lean_ctor_set(v___x_2211_, 1, v_a_2255_);
lean_ctor_set(v___x_2211_, 0, v___x_2266_);
v___x_2268_ = v___x_2211_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_a_2255_);
lean_ctor_set(v_reuseFailAlloc_2275_, 2, v_fvarId_2253_);
lean_ctor_set(v_reuseFailAlloc_2275_, 3, v_a_2259_);
v___x_2268_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2270_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2268_);
v___x_2270_ = v___x_2204_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2272_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2270_);
v___x_2272_ = v___x_2263_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v_a_2259_);
lean_dec(v_a_2255_);
lean_dec(v_fvarId_2253_);
lean_del_object(v___x_2211_);
lean_del_object(v___x_2204_);
v_a_2277_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2260_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2260_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec(v_a_2255_);
lean_dec(v_fvarId_2253_);
lean_del_object(v___x_2211_);
lean_dec(v_typeName_2206_);
lean_del_object(v___x_2204_);
v_a_2285_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2258_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2258_);
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
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_fvarId_2253_);
lean_del_object(v___x_2211_);
lean_dec_ref(v_alts_2209_);
lean_dec(v_typeName_2206_);
lean_del_object(v___x_2204_);
v_a_2293_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2254_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2254_);
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
uint8_t v___x_2301_; lean_object* v___x_2302_; 
lean_del_object(v___x_2211_);
lean_dec_ref(v_alts_2209_);
lean_dec_ref(v_resultType_2207_);
lean_dec(v_typeName_2206_);
lean_del_object(v___x_2204_);
v___x_2301_ = 1;
v___x_2302_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2301_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
return v___x_2302_;
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_del_object(v___x_2211_);
lean_dec_ref(v_alts_2209_);
lean_dec(v_discr_2208_);
lean_dec_ref(v_resultType_2207_);
lean_dec(v_typeName_2206_);
lean_del_object(v___x_2204_);
v_a_2303_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2214_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2214_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2334_; 
v_fvarId_2313_ = lean_ctor_get(v_c_2058_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_c_2058_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2315_ = v_c_2058_;
v_isShared_2316_ = v_isSharedCheck_2334_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_fvarId_2313_);
lean_dec(v_c_2058_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2334_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
uint8_t v___x_2317_; lean_object* v___x_2318_; lean_object* v_subst_2319_; lean_object* v___x_2320_; 
v___x_2317_ = 1;
v___x_2318_ = lean_st_ref_get(v_a_2059_);
v_subst_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc_ref(v_subst_2319_);
lean_dec(v___x_2318_);
v___x_2320_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2319_, v_fvarId_2313_, v___x_2317_);
lean_dec_ref(v_subst_2319_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_fvarId_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2331_; 
v_fvarId_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2331_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_fvarId_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2331_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v_fvarId_2321_);
v___x_2326_ = v___x_2315_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_fvarId_2321_);
v___x_2326_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2328_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2326_);
v___x_2328_ = v___x_2323_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
else
{
uint8_t v___x_2332_; lean_object* v___x_2333_; 
lean_del_object(v___x_2315_);
v___x_2332_ = 1;
v___x_2333_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2332_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
return v___x_2333_;
}
}
}
default: 
{
lean_object* v_type_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2359_; 
v_type_2335_ = lean_ctor_get(v_c_2058_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_c_2058_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2337_ = v_c_2058_;
v_isShared_2338_ = v_isSharedCheck_2359_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_type_2335_);
lean_dec(v_c_2058_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2359_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Compiler_LCNF_toImpureType(v_type_2335_, v_a_2062_, v_a_2063_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2350_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2350_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2350_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v_a_2340_);
v___x_2345_ = v___x_2337_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2347_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2345_);
v___x_2347_ = v___x_2342_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_del_object(v___x_2337_);
v_a_2351_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2339_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2339_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2058_ = stack[0].m_obj;
lean_object* v_a_2059_ = stack[1].m_obj;
lean_object* v_a_2060_ = stack[2].m_obj;
lean_object* v_a_2061_ = stack[3].m_obj;
lean_object* v_a_2062_ = stack[4].m_obj;
lean_object* v_a_2063_ = stack[5].m_obj;
lean_object* v_res_2360_;
v_res_2360_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_c_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
stack->m_obj
 = v_res_2360_;
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(lean_object* v_decl_2361_, lean_object* v_k_2362_, lean_object* v_ctorInfo_2363_, lean_object* v_fields_2364_, lean_object* v_irArgs_2365_, lean_object* v_i_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v___x_2373_; uint8_t v___x_2374_; 
v___x_2373_ = lean_array_get_size(v_irArgs_2365_);
v___x_2374_ = lean_nat_dec_lt(v_i_2366_, v___x_2373_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; 
lean_dec(v_i_2366_);
lean_dec_ref(v_decl_2361_);
v___x_2375_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2362_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_2375_;
}
else
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_array_fget_borrowed(v_irArgs_2365_, v_i_2366_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_unsigned_to_nat(1u);
v___x_2378_ = lean_nat_add(v_i_2366_, v___x_2377_);
lean_dec(v_i_2366_);
v_i_2366_ = v___x_2378_;
goto _start;
}
else
{
lean_object* v_fvarId_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v_fvarId_2380_ = lean_ctor_get(v___x_2376_, 0);
v___x_2381_ = lean_box(0);
v___x_2382_ = lean_array_get_borrowed(v___x_2381_, v_fields_2364_, v_i_2366_);
switch(lean_obj_tag(v___x_2382_))
{
case 2:
{
lean_object* v_i_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v_i_2383_ = lean_ctor_get(v___x_2382_, 0);
v___x_2384_ = lean_unsigned_to_nat(1u);
v___x_2385_ = lean_nat_add(v_i_2366_, v___x_2384_);
lean_dec(v_i_2366_);
lean_inc_ref(v_decl_2361_);
v___x_2386_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2361_, v_k_2362_, v_ctorInfo_2363_, v_fields_2364_, v_irArgs_2365_, v___x_2385_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2405_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2405_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2405_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v_fvarId_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2401_; 
v_fvarId_2391_ = lean_ctor_get(v_decl_2361_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_decl_2361_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; lean_object* v_unused_2403_; lean_object* v_unused_2404_; 
v_unused_2402_ = lean_ctor_get(v_decl_2361_, 3);
lean_dec(v_unused_2402_);
v_unused_2403_ = lean_ctor_get(v_decl_2361_, 2);
lean_dec(v_unused_2403_);
v_unused_2404_ = lean_ctor_get(v_decl_2361_, 1);
lean_dec(v_unused_2404_);
v___x_2393_ = v_decl_2361_;
v_isShared_2394_ = v_isSharedCheck_2401_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_fvarId_2391_);
lean_dec(v_decl_2361_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2401_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
lean_inc(v_fvarId_2380_);
lean_inc(v_i_2383_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set_tag(v___x_2393_, 8);
lean_ctor_set(v___x_2393_, 3, v_a_2387_);
lean_ctor_set(v___x_2393_, 2, v_fvarId_2380_);
lean_ctor_set(v___x_2393_, 1, v_i_2383_);
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_fvarId_2391_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_i_2383_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_fvarId_2380_);
lean_ctor_set(v_reuseFailAlloc_2400_, 3, v_a_2387_);
v___x_2396_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2398_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2396_);
v___x_2398_ = v___x_2389_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_2361_);
return v___x_2386_;
}
}
case 3:
{
lean_object* v_offset_2406_; lean_object* v_type_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v_offset_2406_ = lean_ctor_get(v___x_2382_, 1);
v_type_2407_ = lean_ctor_get(v___x_2382_, 2);
v___x_2408_ = lean_unsigned_to_nat(1u);
v___x_2409_ = lean_nat_add(v_i_2366_, v___x_2408_);
lean_dec(v_i_2366_);
lean_inc_ref(v_decl_2361_);
v___x_2410_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2361_, v_k_2362_, v_ctorInfo_2363_, v_fields_2364_, v_irArgs_2365_, v___x_2409_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2423_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2423_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2423_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v_fvarId_2415_; lean_object* v_size_2416_; lean_object* v_usize_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
v_fvarId_2415_ = lean_ctor_get(v_decl_2361_, 0);
lean_inc(v_fvarId_2415_);
lean_dec_ref(v_decl_2361_);
v_size_2416_ = lean_ctor_get(v_ctorInfo_2363_, 2);
v_usize_2417_ = lean_ctor_get(v_ctorInfo_2363_, 3);
v___x_2418_ = lean_nat_add(v_size_2416_, v_usize_2417_);
lean_inc_ref(v_type_2407_);
lean_inc(v_fvarId_2380_);
lean_inc(v_offset_2406_);
v___x_2419_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_2419_, 0, v_fvarId_2415_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
lean_ctor_set(v___x_2419_, 2, v_offset_2406_);
lean_ctor_set(v___x_2419_, 3, v_fvarId_2380_);
lean_ctor_set(v___x_2419_, 4, v_type_2407_);
lean_ctor_set(v___x_2419_, 5, v_a_2411_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2419_);
v___x_2421_ = v___x_2413_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
else
{
lean_dec_ref(v_decl_2361_);
return v___x_2410_;
}
}
default: 
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = lean_unsigned_to_nat(1u);
v___x_2425_ = lean_nat_add(v_i_2366_, v___x_2424_);
lean_dec(v_i_2366_);
v_i_2366_ = v___x_2425_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2361_ = stack[0].m_obj;
lean_object* v_k_2362_ = stack[1].m_obj;
lean_object* v_ctorInfo_2363_ = stack[2].m_obj;
lean_object* v_fields_2364_ = stack[3].m_obj;
lean_object* v_irArgs_2365_ = stack[4].m_obj;
lean_object* v_i_2366_ = stack[5].m_obj;
lean_object* v_a_2367_ = stack[6].m_obj;
lean_object* v_a_2368_ = stack[7].m_obj;
lean_object* v_a_2369_ = stack[8].m_obj;
lean_object* v_a_2370_ = stack[9].m_obj;
lean_object* v_a_2371_ = stack[10].m_obj;
lean_object* v_res_2427_;
v_res_2427_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2361_, v_k_2362_, v_ctorInfo_2363_, v_fields_2364_, v_irArgs_2365_, v_i_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
stack->m_obj
 = v_res_2427_;
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(lean_object* v_decl_2428_, lean_object* v_k_2429_, lean_object* v_ctorInfo_2430_, lean_object* v_fields_2431_, lean_object* v_irArgs_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_unsigned_to_nat(0u);
v___x_2440_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2428_, v_k_2429_, v_ctorInfo_2430_, v_fields_2431_, v_irArgs_2432_, v___x_2439_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
return v___x_2440_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2428_ = stack[0].m_obj;
lean_object* v_k_2429_ = stack[1].m_obj;
lean_object* v_ctorInfo_2430_ = stack[2].m_obj;
lean_object* v_fields_2431_ = stack[3].m_obj;
lean_object* v_irArgs_2432_ = stack[4].m_obj;
lean_object* v_a_2433_ = stack[5].m_obj;
lean_object* v_a_2434_ = stack[6].m_obj;
lean_object* v_a_2435_ = stack[7].m_obj;
lean_object* v_a_2436_ = stack[8].m_obj;
lean_object* v_a_2437_ = stack[9].m_obj;
lean_object* v_res_2441_;
v_res_2441_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_2428_, v_k_2429_, v_ctorInfo_2430_, v_fields_2431_, v_irArgs_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
stack->m_obj
 = v_res_2441_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(lean_object* v_decl_2442_, lean_object* v_k_2443_, lean_object* v_ctorInfo_2444_, lean_object* v_fields_2445_, lean_object* v_irArgs_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_2442_, v_k_2443_, v_ctorInfo_2444_, v_fields_2445_, v_irArgs_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
lean_dec(v_a_2447_);
lean_dec_ref(v_irArgs_2446_);
lean_dec_ref(v_fields_2445_);
lean_dec_ref(v_ctorInfo_2444_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(lean_object* v_decl_2454_, lean_object* v_k_2455_, lean_object* v_name_2456_, lean_object* v_args_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_2454_, v_k_2455_, v_name_2456_, v_args_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec(v_a_2458_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(lean_object* v_decl_2465_, lean_object* v_k_2466_, lean_object* v_name_2467_, lean_object* v_args_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_2465_, v_k_2466_, v_name_2467_, v_args_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object* v_k_2476_, lean_object* v_fvarId_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_2476_, v_fvarId_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object* v_decl_2485_, lean_object* v_k_2486_, lean_object* v_name_2487_, lean_object* v_numParams_2488_, lean_object* v_args_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_2485_, v_k_2486_, v_name_2487_, v_numParams_2488_, v_args_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec_ref(v_a_2491_);
lean_dec(v_a_2490_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object* v_fvarId_2497_, lean_object* v_sz_2498_, lean_object* v_i_2499_, lean_object* v_bs_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
size_t v_sz_boxed_2507_; size_t v_i_boxed_2508_; lean_object* v_res_2509_; 
v_sz_boxed_2507_ = lean_unbox_usize(v_sz_2498_);
lean_dec(v_sz_2498_);
v_i_boxed_2508_ = lean_unbox_usize(v_i_2499_);
lean_dec(v_i_2499_);
v_res_2509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2497_, v_sz_boxed_2507_, v_i_boxed_2508_, v_bs_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object* v_k_2510_, lean_object* v_decl_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_2510_, v_decl_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object* v_discr_2519_, lean_object* v_alt_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_discr_2519_, v_alt_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* v_decl_2528_, lean_object* v_k_2529_, lean_object* v_ctorInfo_2530_, lean_object* v_fields_2531_, lean_object* v_irArgs_2532_, lean_object* v_i_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2528_, v_k_2529_, v_ctorInfo_2530_, v_fields_2531_, v_irArgs_2532_, v_i_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
lean_dec(v_a_2534_);
lean_dec_ref(v_irArgs_2532_);
lean_dec_ref(v_fields_2531_);
lean_dec_ref(v_ctorInfo_2530_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object* v_decl_2541_, lean_object* v_k_2542_, lean_object* v_name_2543_, lean_object* v_numParams_2544_, lean_object* v_args_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_2541_, v_k_2542_, v_name_2543_, v_numParams_2544_, v_args_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec(v_a_2546_);
lean_dec_ref(v_args_2545_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(lean_object* v_discr_2553_, lean_object* v_k_2554_, lean_object* v_ctorInfo_2555_, lean_object* v_params_2556_, lean_object* v_fields_2557_, lean_object* v_i_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2553_, v_k_2554_, v_ctorInfo_2555_, v_params_2556_, v_fields_2557_, v_i_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_fields_2557_);
lean_dec_ref(v_params_2556_);
lean_dec_ref(v_ctorInfo_2555_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(lean_object* v_c_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_c_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(lean_object* v_decl_2574_, lean_object* v_k_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2574_, v_k_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
lean_dec(v_a_2576_);
return v_res_2582_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(lean_object* v_00_u03b1_2583_, lean_object* v_msg_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_2584_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
return v___x_2591_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2584_ = stack[1].m_obj;
lean_object* v___y_2585_ = stack[2].m_obj;
lean_object* v___y_2586_ = stack[3].m_obj;
lean_object* v___y_2587_ = stack[4].m_obj;
lean_object* v___y_2588_ = stack[5].m_obj;
lean_object* v___y_2589_ = stack[6].m_obj;
lean_object* v_res_2592_;
v_res_2592_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(lean_box(0), v_msg_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
stack->m_obj
 = v_res_2592_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(lean_object* v_00_u03b1_2593_, lean_object* v_msg_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(v_00_u03b1_2593_, v_msg_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
return v_res_2601_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(size_t v_sz_2602_, size_t v_i_2603_, lean_object* v_bs_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2602_, v_i_2603_, v_bs_2604_, v___y_2605_, v___y_2607_, v___y_2608_, v___y_2609_);
return v___x_2611_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2602_ = stack[0].m_num;
size_t v_i_2603_ = stack[1].m_num;
lean_object* v_bs_2604_ = stack[2].m_obj;
lean_object* v___y_2605_ = stack[3].m_obj;
lean_object* v___y_2606_ = stack[4].m_obj;
lean_object* v___y_2607_ = stack[5].m_obj;
lean_object* v___y_2608_ = stack[6].m_obj;
lean_object* v___y_2609_ = stack[7].m_obj;
lean_object* v_res_2612_;
v_res_2612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(v_sz_2602_, v_i_2603_, v_bs_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
stack->m_obj
 = v_res_2612_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(lean_object* v_sz_2613_, lean_object* v_i_2614_, lean_object* v_bs_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
size_t v_sz_boxed_2622_; size_t v_i_boxed_2623_; lean_object* v_res_2624_; 
v_sz_boxed_2622_ = lean_unbox_usize(v_sz_2613_);
lean_dec(v_sz_2613_);
v_i_boxed_2623_ = lean_unbox_usize(v_i_2614_);
lean_dec(v_i_2614_);
v_res_2624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(v_sz_boxed_2622_, v_i_boxed_2623_, v_bs_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
return v_res_2624_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(lean_object* v_as_2625_, size_t v_i_2626_, size_t v_stop_2627_, lean_object* v_b_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_2625_, v_i_2626_, v_stop_2627_, v_b_2628_, v___y_2629_);
return v___x_2635_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2625_ = stack[0].m_obj;
size_t v_i_2626_ = stack[1].m_num;
size_t v_stop_2627_ = stack[2].m_num;
lean_object* v_b_2628_ = stack[3].m_obj;
lean_object* v___y_2629_ = stack[4].m_obj;
lean_object* v___y_2630_ = stack[5].m_obj;
lean_object* v___y_2631_ = stack[6].m_obj;
lean_object* v___y_2632_ = stack[7].m_obj;
lean_object* v___y_2633_ = stack[8].m_obj;
lean_object* v_res_2636_;
v_res_2636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(v_as_2625_, v_i_2626_, v_stop_2627_, v_b_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
stack->m_obj
 = v_res_2636_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(lean_object* v_as_2637_, lean_object* v_i_2638_, lean_object* v_stop_2639_, lean_object* v_b_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
size_t v_i_boxed_2647_; size_t v_stop_boxed_2648_; lean_object* v_res_2649_; 
v_i_boxed_2647_ = lean_unbox_usize(v_i_2638_);
lean_dec(v_i_2638_);
v_stop_boxed_2648_ = lean_unbox_usize(v_stop_2639_);
lean_dec(v_stop_2639_);
v_res_2649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(v_as_2637_, v_i_boxed_2647_, v_stop_boxed_2648_, v_b_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v_as_2637_);
return v_res_2649_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(lean_object* v_upperBound_2650_, lean_object* v_params_2651_, lean_object* v___x_2652_, lean_object* v_discr_2653_, lean_object* v_inst_2654_, lean_object* v_R_2655_, lean_object* v_a_2656_, lean_object* v_b_2657_, lean_object* v_c_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_2650_, v_params_2651_, v___x_2652_, v_discr_2653_, v_a_2656_, v_b_2657_, v___y_2659_);
return v___x_2665_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2650_ = stack[0].m_obj;
lean_object* v_params_2651_ = stack[1].m_obj;
lean_object* v___x_2652_ = stack[2].m_obj;
lean_object* v_discr_2653_ = stack[3].m_obj;
lean_object* v_a_2656_ = stack[6].m_obj;
lean_object* v_b_2657_ = stack[7].m_obj;
lean_object* v___y_2659_ = stack[9].m_obj;
lean_object* v___y_2660_ = stack[10].m_obj;
lean_object* v___y_2661_ = stack[11].m_obj;
lean_object* v___y_2662_ = stack[12].m_obj;
lean_object* v___y_2663_ = stack[13].m_obj;
lean_object* v_res_2666_;
v_res_2666_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(v_upperBound_2650_, v_params_2651_, v___x_2652_, v_discr_2653_, lean_box(0), lean_box(0), v_a_2656_, v_b_2657_, lean_box(0), v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
stack->m_obj
 = v_res_2666_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(lean_object* v_upperBound_2667_, lean_object* v_params_2668_, lean_object* v___x_2669_, lean_object* v_discr_2670_, lean_object* v_inst_2671_, lean_object* v_R_2672_, lean_object* v_a_2673_, lean_object* v_b_2674_, lean_object* v_c_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(v_upperBound_2667_, v_params_2668_, v___x_2669_, v_discr_2670_, v_inst_2671_, v_R_2672_, v_a_2673_, v_b_2674_, v_c_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec(v___x_2669_);
lean_dec_ref(v_params_2668_);
lean_dec(v_upperBound_2667_);
return v_res_2682_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(size_t v_sz_2683_, size_t v_i_2684_, lean_object* v_bs_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_2683_, v_i_2684_, v_bs_2685_, v___y_2686_);
return v___x_2692_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2683_ = stack[0].m_num;
size_t v_i_2684_ = stack[1].m_num;
lean_object* v_bs_2685_ = stack[2].m_obj;
lean_object* v___y_2686_ = stack[3].m_obj;
lean_object* v___y_2687_ = stack[4].m_obj;
lean_object* v___y_2688_ = stack[5].m_obj;
lean_object* v___y_2689_ = stack[6].m_obj;
lean_object* v___y_2690_ = stack[7].m_obj;
lean_object* v_res_2693_;
v_res_2693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(v_sz_2683_, v_i_2684_, v_bs_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
stack->m_obj
 = v_res_2693_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___boxed(lean_object* v_sz_2694_, lean_object* v_i_2695_, lean_object* v_bs_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
size_t v_sz_boxed_2703_; size_t v_i_boxed_2704_; lean_object* v_res_2705_; 
v_sz_boxed_2703_ = lean_unbox_usize(v_sz_2694_);
lean_dec(v_sz_2694_);
v_i_boxed_2704_ = lean_unbox_usize(v_i_2695_);
lean_dec(v_i_2695_);
v_res_2705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(v_sz_boxed_2703_, v_i_boxed_2704_, v_bs_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
return v_res_2705_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(lean_object* v_upperBound_2706_, lean_object* v_fieldInfo_2707_, lean_object* v___x_2708_, lean_object* v_inst_2709_, lean_object* v_R_2710_, lean_object* v_a_2711_, lean_object* v_b_2712_, lean_object* v_c_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_2706_, v_fieldInfo_2707_, v___x_2708_, v_a_2711_, v_b_2712_);
return v___x_2720_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2706_ = stack[0].m_obj;
lean_object* v_fieldInfo_2707_ = stack[1].m_obj;
lean_object* v___x_2708_ = stack[2].m_obj;
lean_object* v_a_2711_ = stack[5].m_obj;
lean_object* v_b_2712_ = stack[6].m_obj;
lean_object* v___y_2714_ = stack[8].m_obj;
lean_object* v___y_2715_ = stack[9].m_obj;
lean_object* v___y_2716_ = stack[10].m_obj;
lean_object* v___y_2717_ = stack[11].m_obj;
lean_object* v___y_2718_ = stack[12].m_obj;
lean_object* v_res_2721_;
v_res_2721_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(v_upperBound_2706_, v_fieldInfo_2707_, v___x_2708_, lean_box(0), lean_box(0), v_a_2711_, v_b_2712_, lean_box(0), v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
stack->m_obj
 = v_res_2721_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(lean_object* v_upperBound_2722_, lean_object* v_fieldInfo_2723_, lean_object* v___x_2724_, lean_object* v_inst_2725_, lean_object* v_R_2726_, lean_object* v_a_2727_, lean_object* v_b_2728_, lean_object* v_c_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(v_upperBound_2722_, v_fieldInfo_2723_, v___x_2724_, v_inst_2725_, v_R_2726_, v_a_2727_, v_b_2728_, v_c_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___x_2724_);
lean_dec_ref(v_fieldInfo_2723_);
lean_dec(v_upperBound_2722_);
return v_res_2736_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0));
v___x_2739_ = l_Lean_stringToMessageData(v___x_2738_);
return v___x_2739_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3(void){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2));
v___x_2742_ = l_Lean_stringToMessageData(v___x_2741_);
return v___x_2742_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4));
v___x_2745_ = l_Lean_stringToMessageData(v___x_2744_);
return v___x_2745_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7(void){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2747_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6));
v___x_2748_ = l_Lean_stringToMessageData(v___x_2747_);
return v___x_2748_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(lean_object* v_decl_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_toSignature_2756_; lean_object* v_value_2757_; uint8_t v_recursive_2758_; lean_object* v_inlineAttr_x3f_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2891_; 
v_toSignature_2756_ = lean_ctor_get(v_decl_2749_, 0);
v_value_2757_ = lean_ctor_get(v_decl_2749_, 1);
v_recursive_2758_ = lean_ctor_get_uint8(v_decl_2749_, sizeof(void*)*3);
v_inlineAttr_x3f_2759_ = lean_ctor_get(v_decl_2749_, 2);
v_isSharedCheck_2891_ = !lean_is_exclusive(v_decl_2749_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2761_ = v_decl_2749_;
v_isShared_2762_ = v_isSharedCheck_2891_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_inlineAttr_x3f_2759_);
lean_inc(v_value_2757_);
lean_inc(v_toSignature_2756_);
lean_dec(v_decl_2749_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2891_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v_name_2763_; lean_object* v_levelParams_2764_; lean_object* v_type_2765_; lean_object* v_params_2766_; uint8_t v_safe_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2890_; 
v_name_2763_ = lean_ctor_get(v_toSignature_2756_, 0);
v_levelParams_2764_ = lean_ctor_get(v_toSignature_2756_, 1);
v_type_2765_ = lean_ctor_get(v_toSignature_2756_, 2);
v_params_2766_ = lean_ctor_get(v_toSignature_2756_, 3);
v_safe_2767_ = lean_ctor_get_uint8(v_toSignature_2756_, sizeof(void*)*4);
v_isSharedCheck_2890_ = !lean_is_exclusive(v_toSignature_2756_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2769_ = v_toSignature_2756_;
v_isShared_2770_ = v_isSharedCheck_2890_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_params_2766_);
lean_inc(v_type_2765_);
lean_inc(v_levelParams_2764_);
lean_inc(v_name_2763_);
lean_dec(v_toSignature_2756_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2890_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
size_t v_sz_2771_; size_t v___x_2772_; lean_object* v___x_2773_; 
v_sz_2771_ = lean_array_size(v_params_2766_);
v___x_2772_ = ((size_t)0ULL);
lean_inc_ref(v_params_2766_);
v___x_2773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2771_, v___x_2772_, v_params_2766_, v_a_2750_, v_a_2752_, v_a_2753_, v_a_2754_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = lean_array_get_size(v_params_2766_);
lean_dec_ref(v_params_2766_);
v___x_2776_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2765_, v___x_2775_, v_a_2753_, v_a_2754_);
lean_dec_ref(v_type_2765_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2873_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2873_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2873_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; lean_object* v_env_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2781_ = lean_st_ref_get(v_a_2754_);
v_env_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc_ref(v_env_2782_);
lean_dec(v___x_2781_);
v___x_2783_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
lean_inc(v_name_2763_);
v___x_2784_ = l_Lean_TagAttribute_hasTag(v___x_2783_, v_env_2782_, v_name_2763_);
if (lean_obj_tag(v_value_2757_) == 0)
{
lean_object* v_code_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2835_; 
lean_del_object(v___x_2779_);
v_code_2785_ = lean_ctor_get(v_value_2757_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_value_2757_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2787_ = v_value_2757_;
v_isShared_2788_ = v_isSharedCheck_2835_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_code_2785_);
lean_dec(v_value_2757_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2835_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; 
if (v___x_2784_ == 0)
{
v___y_2790_ = v_a_2750_;
v___y_2791_ = v_a_2751_;
v___y_2792_ = v_a_2752_;
v___y_2793_ = v_a_2753_;
v___y_2794_ = v_a_2754_;
goto v___jp_2789_;
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_del_object(v___x_2787_);
lean_dec_ref(v_code_2785_);
lean_dec(v_a_2777_);
lean_dec(v_a_2774_);
lean_del_object(v___x_2769_);
lean_dec(v_levelParams_2764_);
lean_del_object(v___x_2761_);
lean_dec(v_inlineAttr_x3f_2759_);
v___x_2821_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1);
v___x_2822_ = l_Lean_MessageData_ofName(v_name_2763_);
v___x_2823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2821_);
lean_ctor_set(v___x_2823_, 1, v___x_2822_);
v___x_2824_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3);
v___x_2825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2823_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2825_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
v___jp_2789_:
{
lean_object* v___x_2795_; 
v___x_2795_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_2785_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2812_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2812_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2812_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 3, v_a_2774_);
lean_ctor_set(v___x_2769_, 2, v_a_2777_);
v___x_2801_ = v___x_2769_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_name_2763_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_levelParams_2764_);
lean_ctor_set(v_reuseFailAlloc_2811_, 2, v_a_2777_);
lean_ctor_set(v_reuseFailAlloc_2811_, 3, v_a_2774_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, sizeof(void*)*4, v_safe_2767_);
v___x_2801_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2803_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v_a_2796_);
v___x_2803_ = v___x_2787_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2796_);
v___x_2803_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
lean_object* v___x_2805_; 
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 1, v___x_2803_);
lean_ctor_set(v___x_2761_, 0, v___x_2801_);
v___x_2805_ = v___x_2761_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2801_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v___x_2803_);
lean_ctor_set(v_reuseFailAlloc_2809_, 2, v_inlineAttr_x3f_2759_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*3, v_recursive_2758_);
v___x_2805_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
lean_object* v___x_2807_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2805_);
v___x_2807_ = v___x_2798_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_del_object(v___x_2787_);
lean_dec(v_a_2777_);
lean_dec(v_a_2774_);
lean_del_object(v___x_2769_);
lean_dec(v_levelParams_2764_);
lean_dec(v_name_2763_);
lean_del_object(v___x_2761_);
lean_dec(v_inlineAttr_x3f_2759_);
v_a_2813_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2795_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2795_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
}
else
{
lean_object* v_externAttrData_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2872_; 
v_externAttrData_2836_ = lean_ctor_get(v_value_2757_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_value_2757_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2838_ = v_value_2757_;
v_isShared_2839_ = v_isSharedCheck_2872_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_externAttrData_2836_);
lean_dec(v_value_2757_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2872_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v_resultType_2841_; 
if (v___x_2784_ == 0)
{
v_resultType_2841_ = v_a_2777_;
goto v___jp_2840_;
}
else
{
uint8_t v___x_2854_; 
v___x_2854_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_2777_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_dec(v_a_2777_);
v___x_2855_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
v_resultType_2841_ = v___x_2855_;
goto v___jp_2840_;
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_del_object(v___x_2838_);
lean_dec(v_externAttrData_2836_);
lean_del_object(v___x_2779_);
lean_dec(v_a_2774_);
lean_del_object(v___x_2769_);
lean_dec(v_levelParams_2764_);
lean_del_object(v___x_2761_);
lean_dec(v_inlineAttr_x3f_2759_);
v___x_2856_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5);
v___x_2857_ = l_Lean_MessageData_ofName(v_name_2763_);
v___x_2858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7);
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2858_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = l_Lean_MessageData_ofExpr(v_a_2777_);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2862_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
v___jp_2840_:
{
lean_object* v___x_2843_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 3, v_a_2774_);
lean_ctor_set(v___x_2769_, 2, v_resultType_2841_);
v___x_2843_ = v___x_2769_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_name_2763_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_levelParams_2764_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_resultType_2841_);
lean_ctor_set(v_reuseFailAlloc_2853_, 3, v_a_2774_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, sizeof(void*)*4, v_safe_2767_);
v___x_2843_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2845_; 
if (v_isShared_2839_ == 0)
{
v___x_2845_ = v___x_2838_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_externAttrData_2836_);
v___x_2845_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2847_; 
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 1, v___x_2845_);
lean_ctor_set(v___x_2761_, 0, v___x_2843_);
v___x_2847_ = v___x_2761_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v___x_2845_);
lean_ctor_set(v_reuseFailAlloc_2851_, 2, v_inlineAttr_x3f_2759_);
lean_ctor_set_uint8(v_reuseFailAlloc_2851_, sizeof(void*)*3, v_recursive_2758_);
v___x_2847_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
lean_object* v___x_2849_; 
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2847_);
v___x_2849_ = v___x_2779_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2847_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
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
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v_a_2774_);
lean_del_object(v___x_2769_);
lean_dec(v_levelParams_2764_);
lean_dec(v_name_2763_);
lean_del_object(v___x_2761_);
lean_dec(v_inlineAttr_x3f_2759_);
lean_dec_ref(v_value_2757_);
v_a_2874_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2776_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2776_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_del_object(v___x_2769_);
lean_dec_ref(v_params_2766_);
lean_dec_ref(v_type_2765_);
lean_dec(v_levelParams_2764_);
lean_dec(v_name_2763_);
lean_del_object(v___x_2761_);
lean_dec(v_inlineAttr_x3f_2759_);
lean_dec_ref(v_value_2757_);
v_a_2882_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2773_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2773_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2749_ = stack[0].m_obj;
lean_object* v_a_2750_ = stack[1].m_obj;
lean_object* v_a_2751_ = stack[2].m_obj;
lean_object* v_a_2752_ = stack[3].m_obj;
lean_object* v_a_2753_ = stack[4].m_obj;
lean_object* v_a_2754_ = stack[5].m_obj;
lean_object* v_res_2892_;
v_res_2892_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
stack->m_obj
 = v_res_2892_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___boxed(lean_object* v_decl_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
return v_res_2900_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(lean_object* v_decl_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v___x_2910_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc_n(v_a_2909_, 2);
lean_dec_ref_known(v___x_2908_, 1);
v___x_2910_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_2909_, v_a_2906_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2917_ == 0)
{
lean_object* v_unused_2918_; 
v_unused_2918_ = lean_ctor_get(v___x_2910_, 0);
lean_dec(v_unused_2918_);
v___x_2912_ = v___x_2910_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_dec(v___x_2910_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v_a_2909_);
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2909_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec(v_a_2909_);
v_a_2919_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2910_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2910_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
else
{
return v___x_2908_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2901_ = stack[0].m_obj;
lean_object* v_a_2902_ = stack[1].m_obj;
lean_object* v_a_2903_ = stack[2].m_obj;
lean_object* v_a_2904_ = stack[3].m_obj;
lean_object* v_a_2905_ = stack[4].m_obj;
lean_object* v_a_2906_ = stack[5].m_obj;
lean_object* v_res_2927_;
v_res_2927_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
stack->m_obj
 = v_res_2927_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go___boxed(lean_object* v_decl_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
return v_res_2935_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_box(0);
v___x_2937_ = lean_unsigned_to_nat(16u);
v___x_2938_ = lean_mk_array(v___x_2937_, v___x_2936_);
return v___x_2938_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2939_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0);
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
lean_ctor_set(v___x_2941_, 1, v___x_2939_);
return v___x_2941_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2(void){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1);
v___x_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
return v___x_2943_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(lean_object* v_decl_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2);
v___x_2951_ = lean_st_mk_ref(v___x_2950_);
v___x_2952_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_2944_, v___x_2951_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2961_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_2961_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2961_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2957_ = lean_st_ref_get(v___x_2951_);
lean_dec(v___x_2951_);
lean_dec(v___x_2957_);
if (v_isShared_2956_ == 0)
{
v___x_2959_ = v___x_2955_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2953_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
else
{
lean_dec(v___x_2951_);
return v___x_2952_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2944_ = stack[0].m_obj;
lean_object* v_a_2945_ = stack[1].m_obj;
lean_object* v_a_2946_ = stack[2].m_obj;
lean_object* v_a_2947_ = stack[3].m_obj;
lean_object* v_a_2948_ = stack[4].m_obj;
lean_object* v_res_2962_;
v_res_2962_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_decl_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
stack->m_obj
 = v_res_2962_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___boxed(lean_object* v_decl_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_decl_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_);
lean_dec(v_a_2967_);
lean_dec_ref(v_a_2966_);
lean_dec(v_a_2965_);
lean_dec_ref(v_a_2964_);
return v_res_2969_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(size_t v_sz_2970_, size_t v_i_2971_, lean_object* v_bs_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
uint8_t v___x_2978_; 
v___x_2978_ = lean_usize_dec_lt(v_i_2971_, v_sz_2970_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
v___x_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_bs_2972_);
return v___x_2979_;
}
else
{
lean_object* v_v_2980_; lean_object* v___x_2981_; lean_object* v_bs_x27_2982_; lean_object* v___x_2983_; 
v_v_2980_ = lean_array_uget(v_bs_2972_, v_i_2971_);
v___x_2981_ = lean_unsigned_to_nat(0u);
v_bs_x27_2982_ = lean_array_uset(v_bs_2972_, v_i_2971_, v___x_2981_);
v___x_2983_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_v_2980_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; size_t v___x_2985_; size_t v___x_2986_; lean_object* v___x_2987_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2985_ = ((size_t)1ULL);
v___x_2986_ = lean_usize_add(v_i_2971_, v___x_2985_);
v___x_2987_ = lean_array_uset(v_bs_x27_2982_, v_i_2971_, v_a_2984_);
v_i_2971_ = v___x_2986_;
v_bs_2972_ = v___x_2987_;
goto _start;
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v_bs_x27_2982_);
v_a_2989_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2983_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2983_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2970_ = stack[0].m_num;
size_t v_i_2971_ = stack[1].m_num;
lean_object* v_bs_2972_ = stack[2].m_obj;
lean_object* v___y_2973_ = stack[3].m_obj;
lean_object* v___y_2974_ = stack[4].m_obj;
lean_object* v___y_2975_ = stack[5].m_obj;
lean_object* v___y_2976_ = stack[6].m_obj;
lean_object* v_res_2997_;
v_res_2997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_2970_, v_i_2971_, v_bs_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
stack->m_obj
 = v_res_2997_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0___boxed(lean_object* v_sz_2998_, lean_object* v_i_2999_, lean_object* v_bs_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
size_t v_sz_boxed_3006_; size_t v_i_boxed_3007_; lean_object* v_res_3008_; 
v_sz_boxed_3006_ = lean_unbox_usize(v_sz_2998_);
lean_dec(v_sz_2998_);
v_i_boxed_3007_ = lean_unbox_usize(v_i_2999_);
lean_dec(v_i_2999_);
v_res_3008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_boxed_3006_, v_i_boxed_3007_, v_bs_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
return v_res_3008_;
}
}
lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0(lean_object* v_x_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
size_t v_sz_3015_; size_t v___x_3016_; lean_object* v___x_3017_; 
v_sz_3015_ = lean_array_size(v_x_3009_);
v___x_3016_ = ((size_t)0ULL);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_3015_, v___x_3016_, v_x_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
return v___x_3017_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_toImpure___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3009_ = stack[0].m_obj;
lean_object* v___y_3010_ = stack[1].m_obj;
lean_object* v___y_3011_ = stack[2].m_obj;
lean_object* v___y_3012_ = stack[3].m_obj;
lean_object* v___y_3013_ = stack[4].m_obj;
lean_object* v_res_3018_;
v_res_3018_ = l_Lean_Compiler_LCNF_toImpure___lam__0(v_x_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
stack->m_obj
 = v_res_3018_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0___boxed(lean_object* v_x_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_Compiler_LCNF_toImpure___lam__0(v_x_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
return v_res_3025_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3076_; uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3076_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3077_ = 1;
v___x_3078_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3079_ = l_Lean_registerTraceClass(v___x_3076_, v___x_3077_, v___x_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3080_;
v_res_3080_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3080_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2____boxed(lean_object* v_a_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
return v_res_3082_;
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
