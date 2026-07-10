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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
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
static const lean_array_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_214_ = lean_st_ref_set(v___y_199_, v___x_213_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(lean_object* v_a_229_, lean_object* v_b_230_, lean_object* v_x_231_){
_start:
{
if (lean_obj_tag(v_x_231_) == 0)
{
lean_dec(v_b_230_);
lean_dec(v_a_229_);
return v_x_231_;
}
else
{
lean_object* v_key_232_; lean_object* v_value_233_; lean_object* v_tail_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_246_; 
v_key_232_ = lean_ctor_get(v_x_231_, 0);
v_value_233_ = lean_ctor_get(v_x_231_, 1);
v_tail_234_ = lean_ctor_get(v_x_231_, 2);
v_isSharedCheck_246_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_246_ == 0)
{
v___x_236_ = v_x_231_;
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_tail_234_);
lean_inc(v_value_233_);
lean_inc(v_key_232_);
lean_dec(v_x_231_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
uint8_t v___x_238_; 
v___x_238_ = l_Lean_instBEqFVarId_beq(v_key_232_, v_a_229_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_229_, v_b_230_, v_tail_234_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 2, v___x_239_);
v___x_241_ = v___x_236_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_key_232_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_value_233_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
else
{
lean_object* v___x_244_; 
lean_dec(v_value_233_);
lean_dec(v_key_232_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 1, v_b_230_);
lean_ctor_set(v___x_236_, 0, v_a_229_);
v___x_244_ = v___x_236_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_229_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_b_230_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_tail_234_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
return v_x_247_;
}
else
{
lean_object* v_key_249_; lean_object* v_value_250_; lean_object* v_tail_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_274_; 
v_key_249_ = lean_ctor_get(v_x_248_, 0);
v_value_250_ = lean_ctor_get(v_x_248_, 1);
v_tail_251_ = lean_ctor_get(v_x_248_, 2);
v_isSharedCheck_274_ = !lean_is_exclusive(v_x_248_);
if (v_isSharedCheck_274_ == 0)
{
v___x_253_ = v_x_248_;
v_isShared_254_ = v_isSharedCheck_274_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_tail_251_);
lean_inc(v_value_250_);
lean_inc(v_key_249_);
lean_dec(v_x_248_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_274_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; uint64_t v_fold_259_; uint64_t v___x_260_; uint64_t v___x_261_; uint64_t v___x_262_; size_t v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_255_ = lean_array_get_size(v_x_247_);
v___x_256_ = l_Lean_instHashableFVarId_hash(v_key_249_);
v___x_257_ = 32ULL;
v___x_258_ = lean_uint64_shift_right(v___x_256_, v___x_257_);
v_fold_259_ = lean_uint64_xor(v___x_256_, v___x_258_);
v___x_260_ = 16ULL;
v___x_261_ = lean_uint64_shift_right(v_fold_259_, v___x_260_);
v___x_262_ = lean_uint64_xor(v_fold_259_, v___x_261_);
v___x_263_ = lean_uint64_to_usize(v___x_262_);
v___x_264_ = lean_usize_of_nat(v___x_255_);
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_sub(v___x_264_, v___x_265_);
v___x_267_ = lean_usize_land(v___x_263_, v___x_266_);
v___x_268_ = lean_array_uget_borrowed(v_x_247_, v___x_267_);
lean_inc(v___x_268_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 2, v___x_268_);
v___x_270_ = v___x_253_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_key_249_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_value_250_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v___x_268_);
v___x_270_ = v_reuseFailAlloc_273_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_271_; 
v___x_271_ = lean_array_uset(v_x_247_, v___x_267_, v___x_270_);
v_x_247_ = v___x_271_;
v_x_248_ = v_tail_251_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(lean_object* v_i_275_, lean_object* v_source_276_, lean_object* v_target_277_){
_start:
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_array_get_size(v_source_276_);
v___x_279_ = lean_nat_dec_lt(v_i_275_, v___x_278_);
if (v___x_279_ == 0)
{
lean_dec_ref(v_source_276_);
lean_dec(v_i_275_);
return v_target_277_;
}
else
{
lean_object* v_es_280_; lean_object* v___x_281_; lean_object* v_source_282_; lean_object* v_target_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_es_280_ = lean_array_fget(v_source_276_, v_i_275_);
v___x_281_ = lean_box(0);
v_source_282_ = lean_array_fset(v_source_276_, v_i_275_, v___x_281_);
v_target_283_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_target_277_, v_es_280_);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_add(v_i_275_, v___x_284_);
lean_dec(v_i_275_);
v_i_275_ = v___x_285_;
v_source_276_ = v_source_282_;
v_target_277_ = v_target_283_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(lean_object* v_data_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_nbuckets_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_288_ = lean_array_get_size(v_data_287_);
v___x_289_ = lean_unsigned_to_nat(2u);
v_nbuckets_290_ = lean_nat_mul(v___x_288_, v___x_289_);
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_box(0);
v___x_293_ = lean_mk_array(v_nbuckets_290_, v___x_292_);
v___x_294_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v___x_291_, v_data_287_, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(lean_object* v_a_295_, lean_object* v_x_296_){
_start:
{
if (lean_obj_tag(v_x_296_) == 0)
{
uint8_t v___x_297_; 
v___x_297_ = 0;
return v___x_297_;
}
else
{
lean_object* v_key_298_; lean_object* v_tail_299_; uint8_t v___x_300_; 
v_key_298_ = lean_ctor_get(v_x_296_, 0);
v_tail_299_ = lean_ctor_get(v_x_296_, 2);
v___x_300_ = l_Lean_instBEqFVarId_beq(v_key_298_, v_a_295_);
if (v___x_300_ == 0)
{
v_x_296_ = v_tail_299_;
goto _start;
}
else
{
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg___boxed(lean_object* v_a_302_, lean_object* v_x_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_302_, v_x_303_);
lean_dec(v_x_303_);
lean_dec(v_a_302_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(lean_object* v_m_306_, lean_object* v_a_307_, lean_object* v_b_308_){
_start:
{
lean_object* v_size_309_; lean_object* v_buckets_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_353_; 
v_size_309_ = lean_ctor_get(v_m_306_, 0);
v_buckets_310_ = lean_ctor_get(v_m_306_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v_m_306_);
if (v_isSharedCheck_353_ == 0)
{
v___x_312_ = v_m_306_;
v_isShared_313_ = v_isSharedCheck_353_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_buckets_310_);
lean_inc(v_size_309_);
lean_dec(v_m_306_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_353_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v_fold_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v_bkt_327_; uint8_t v___x_328_; 
v___x_314_ = lean_array_get_size(v_buckets_310_);
v___x_315_ = l_Lean_instHashableFVarId_hash(v_a_307_);
v___x_316_ = 32ULL;
v___x_317_ = lean_uint64_shift_right(v___x_315_, v___x_316_);
v_fold_318_ = lean_uint64_xor(v___x_315_, v___x_317_);
v___x_319_ = 16ULL;
v___x_320_ = lean_uint64_shift_right(v_fold_318_, v___x_319_);
v___x_321_ = lean_uint64_xor(v_fold_318_, v___x_320_);
v___x_322_ = lean_uint64_to_usize(v___x_321_);
v___x_323_ = lean_usize_of_nat(v___x_314_);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_sub(v___x_323_, v___x_324_);
v___x_326_ = lean_usize_land(v___x_322_, v___x_325_);
v_bkt_327_ = lean_array_uget_borrowed(v_buckets_310_, v___x_326_);
v___x_328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_307_, v_bkt_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v_size_x27_330_; lean_object* v___x_331_; lean_object* v_buckets_x27_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v_size_x27_330_ = lean_nat_add(v_size_309_, v___x_329_);
lean_dec(v_size_309_);
lean_inc(v_bkt_327_);
v___x_331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_331_, 0, v_a_307_);
lean_ctor_set(v___x_331_, 1, v_b_308_);
lean_ctor_set(v___x_331_, 2, v_bkt_327_);
v_buckets_x27_332_ = lean_array_uset(v_buckets_310_, v___x_326_, v___x_331_);
v___x_333_ = lean_unsigned_to_nat(4u);
v___x_334_ = lean_nat_mul(v_size_x27_330_, v___x_333_);
v___x_335_ = lean_unsigned_to_nat(3u);
v___x_336_ = lean_nat_div(v___x_334_, v___x_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_array_get_size(v_buckets_x27_332_);
v___x_338_ = lean_nat_dec_le(v___x_336_, v___x_337_);
lean_dec(v___x_336_);
if (v___x_338_ == 0)
{
lean_object* v_val_339_; lean_object* v___x_341_; 
v_val_339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_buckets_x27_332_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v_val_339_);
lean_ctor_set(v___x_312_, 0, v_size_x27_330_);
v___x_341_ = v___x_312_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_size_x27_330_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_val_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
else
{
lean_object* v___x_344_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v_buckets_x27_332_);
lean_ctor_set(v___x_312_, 0, v_size_x27_330_);
v___x_344_ = v___x_312_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_size_x27_330_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_buckets_x27_332_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
lean_object* v___x_346_; lean_object* v_buckets_x27_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
lean_inc(v_bkt_327_);
v___x_346_ = lean_box(0);
v_buckets_x27_347_ = lean_array_uset(v_buckets_310_, v___x_326_, v___x_346_);
v___x_348_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_307_, v_b_308_, v_bkt_327_);
v___x_349_ = lean_array_uset(v_buckets_x27_347_, v___x_326_, v___x_348_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v___x_349_);
v___x_351_ = v___x_312_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_size_309_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(lean_object* v_p_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_fvarId_360_; lean_object* v_binderName_361_; lean_object* v_type_362_; uint8_t v_borrow_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_419_; 
v_fvarId_360_ = lean_ctor_get(v_p_354_, 0);
v_binderName_361_ = lean_ctor_get(v_p_354_, 1);
v_type_362_ = lean_ctor_get(v_p_354_, 2);
v_borrow_363_ = lean_ctor_get_uint8(v_p_354_, sizeof(void*)*3);
v_isSharedCheck_419_ = !lean_is_exclusive(v_p_354_);
if (v_isSharedCheck_419_ == 0)
{
v___x_365_ = v_p_354_;
v_isShared_366_ = v_isSharedCheck_419_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_type_362_);
lean_inc(v_binderName_361_);
lean_inc(v_fvarId_360_);
lean_dec(v_p_354_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_419_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Compiler_LCNF_toImpureType(v_type_362_, v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_410_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_410_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_410_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_410_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___y_373_; uint8_t v___y_394_; uint8_t v___x_408_; 
v___x_408_ = l_Lean_Expr_isVoid(v_a_368_);
if (v___x_408_ == 0)
{
uint8_t v___x_409_; 
v___x_409_ = l_Lean_Expr_isErased(v_a_368_);
v___y_394_ = v___x_409_;
goto v___jp_393_;
}
else
{
v___y_394_ = v___x_408_;
goto v___jp_393_;
}
v___jp_372_:
{
lean_object* v___x_374_; lean_object* v_lctx_375_; lean_object* v_nextIdx_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_392_; 
v___x_374_ = lean_st_ref_take(v___y_373_);
v_lctx_375_ = lean_ctor_get(v___x_374_, 0);
v_nextIdx_376_ = lean_ctor_get(v___x_374_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_392_ == 0)
{
v___x_378_ = v___x_374_;
v_isShared_379_ = v_isSharedCheck_392_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_nextIdx_376_);
lean_inc(v_lctx_375_);
lean_dec(v___x_374_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_392_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
uint8_t v___x_380_; lean_object* v___x_382_; 
v___x_380_ = 1;
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 2, v_a_368_);
v___x_382_ = v___x_365_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_fvarId_360_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_binderName_361_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v_a_368_);
lean_ctor_set_uint8(v_reuseFailAlloc_391_, sizeof(void*)*3, v_borrow_363_);
v___x_382_ = v_reuseFailAlloc_391_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; lean_object* v___x_385_; 
lean_inc_ref(v___x_382_);
v___x_383_ = l_Lean_Compiler_LCNF_LCtx_addParam(v___x_380_, v_lctx_375_, v___x_382_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_383_);
v___x_385_ = v___x_378_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_383_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_nextIdx_376_);
v___x_385_ = v_reuseFailAlloc_390_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_st_ref_set(v___y_373_, v___x_385_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_382_);
v___x_388_ = v___x_370_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_382_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
v___jp_393_:
{
if (v___y_394_ == 0)
{
v___y_373_ = v_a_356_;
goto v___jp_372_;
}
else
{
lean_object* v___x_395_; lean_object* v_subst_396_; lean_object* v_jpParamMask_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_407_; 
v___x_395_ = lean_st_ref_take(v_a_355_);
v_subst_396_ = lean_ctor_get(v___x_395_, 0);
v_jpParamMask_397_ = lean_ctor_get(v___x_395_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_407_ == 0)
{
v___x_399_ = v___x_395_;
v_isShared_400_ = v_isSharedCheck_407_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_jpParamMask_397_);
lean_inc(v_subst_396_);
lean_dec(v___x_395_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_407_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_401_ = lean_box(0);
lean_inc(v_fvarId_360_);
v___x_402_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_396_, v_fvarId_360_, v___x_401_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_402_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_jpParamMask_397_);
v___x_404_ = v_reuseFailAlloc_406_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; 
v___x_405_ = lean_st_ref_set(v_a_355_, v___x_404_);
v___y_373_ = v_a_356_;
goto v___jp_372_;
}
}
}
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_del_object(v___x_365_);
lean_dec(v_binderName_361_);
lean_dec(v_fvarId_360_);
v_a_411_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_367_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_367_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg___boxed(lean_object* v_p_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec(v_a_421_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(lean_object* v_p_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_427_, v_a_428_, v_a_430_, v_a_431_, v_a_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___boxed(lean_object* v_p_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(v_p_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(lean_object* v_00_u03b2_443_, lean_object* v_m_444_, lean_object* v_a_445_, lean_object* v_b_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_m_444_, v_a_445_, v_b_446_);
return v___x_447_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(lean_object* v_00_u03b2_448_, lean_object* v_a_449_, lean_object* v_x_450_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_449_, v_x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___boxed(lean_object* v_00_u03b2_452_, lean_object* v_a_453_, lean_object* v_x_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(v_00_u03b2_452_, v_a_453_, v_x_454_);
lean_dec(v_x_454_);
lean_dec(v_a_453_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1(lean_object* v_00_u03b2_457_, lean_object* v_data_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_data_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2(lean_object* v_00_u03b2_460_, lean_object* v_a_461_, lean_object* v_b_462_, lean_object* v_x_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_461_, v_b_462_, v_x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_465_, lean_object* v_i_466_, lean_object* v_source_467_, lean_object* v_target_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v_i_466_, v_source_467_, v_target_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_470_, lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_x_471_, v_x_472_);
return v___x_473_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_box(0);
v___x_478_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_479_ = l_Lean_Expr_const___override(v___x_478_, v___x_477_);
return v___x_479_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2);
v___x_481_ = lean_box(1);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___x_480_);
return v___x_482_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_box(0);
v___x_487_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5));
v___x_488_ = l_Lean_Expr_const___override(v___x_487_, v___x_486_);
return v___x_488_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_box(0);
v___x_493_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8));
v___x_494_ = l_Lean_Expr_const___override(v___x_493_, v___x_492_);
return v___x_494_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9);
v___x_496_ = lean_box(1);
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v___x_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(lean_object* v_base_498_, lean_object* v_ctorInfo_499_, lean_object* v_field_500_){
_start:
{
switch(lean_obj_tag(v_field_500_))
{
case 0:
{
lean_object* v___x_501_; 
lean_dec(v_base_498_);
v___x_501_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3);
return v___x_501_;
}
case 1:
{
lean_object* v_i_502_; lean_object* v_type_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_511_; 
v_i_502_ = lean_ctor_get(v_field_500_, 0);
v_type_503_ = lean_ctor_get(v_field_500_, 1);
v_isSharedCheck_511_ = !lean_is_exclusive(v_field_500_);
if (v_isSharedCheck_511_ == 0)
{
v___x_505_ = v_field_500_;
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_type_503_);
lean_inc(v_i_502_);
lean_dec(v_field_500_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set_tag(v___x_505_, 6);
lean_ctor_set(v___x_505_, 1, v_base_498_);
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_i_502_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_base_498_);
v___x_508_ = v_reuseFailAlloc_510_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_type_503_);
return v___x_509_;
}
}
}
case 2:
{
lean_object* v_i_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_i_512_ = lean_ctor_get(v_field_500_, 0);
lean_inc(v_i_512_);
lean_dec_ref_known(v_field_500_, 1);
v___x_513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_513_, 0, v_i_512_);
lean_ctor_set(v___x_513_, 1, v_base_498_);
v___x_514_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
return v___x_515_;
}
case 3:
{
lean_object* v_offset_516_; lean_object* v_type_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_528_; 
v_offset_516_ = lean_ctor_get(v_field_500_, 1);
v_type_517_ = lean_ctor_get(v_field_500_, 2);
v_isSharedCheck_528_ = !lean_is_exclusive(v_field_500_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v_field_500_, 0);
lean_dec(v_unused_529_);
v___x_519_ = v_field_500_;
v_isShared_520_ = v_isSharedCheck_528_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_type_517_);
lean_inc(v_offset_516_);
lean_dec(v_field_500_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_528_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_size_521_; lean_object* v_usize_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
v_size_521_ = lean_ctor_get(v_ctorInfo_499_, 2);
v_usize_522_ = lean_ctor_get(v_ctorInfo_499_, 3);
v___x_523_ = lean_nat_add(v_size_521_, v_usize_522_);
if (v_isShared_520_ == 0)
{
lean_ctor_set_tag(v___x_519_, 8);
lean_ctor_set(v___x_519_, 2, v_base_498_);
lean_ctor_set(v___x_519_, 0, v___x_523_);
v___x_525_ = v___x_519_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_offset_516_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_base_498_);
v___x_525_ = v_reuseFailAlloc_527_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; 
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v_type_517_);
return v___x_526_;
}
}
}
default: 
{
lean_object* v___x_530_; 
lean_dec(v_base_498_);
v___x_530_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___boxed(lean_object* v_base_531_, lean_object* v_ctorInfo_532_, lean_object* v_field_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_base_531_, v_ctorInfo_532_, v_field_533_);
lean_dec_ref(v_ctorInfo_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(lean_object* v_arg_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; lean_object* v_subst_539_; uint8_t v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; 
v___x_538_ = lean_st_ref_get(v_a_536_);
v_subst_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc_ref(v_subst_539_);
lean_dec(v___x_538_);
v___x_540_ = 0;
v___x_541_ = 1;
v___x_542_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v___x_540_, v_subst_539_, v_arg_535_, v___x_541_);
lean_dec_ref(v_subst_539_);
if (lean_obj_tag(v___x_542_) == 1)
{
lean_object* v_fvarId_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_551_; 
v_fvarId_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_551_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_fvarId_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_fvarId_543_);
v___x_548_ = v_reuseFailAlloc_550_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; 
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v___x_542_);
v___x_552_ = lean_box(0);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg___boxed(lean_object* v_arg_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_554_, v_a_555_);
lean_dec(v_a_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(lean_object* v_arg_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_558_, v_a_559_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___boxed(lean_object* v_arg_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(v_arg_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(lean_object* v_msg_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = l_Lean_instInhabitedExpr;
v___x_576_ = lean_panic_fn_borrowed(v___x_575_, v_msg_574_);
return v___x_576_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_580_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2));
v___x_581_ = lean_unsigned_to_nat(11u);
v___x_582_ = lean_unsigned_to_nat(83u);
v___x_583_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1));
v___x_584_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_585_ = l_mkPanicMessageWithDecl(v___x_584_, v___x_583_, v___x_582_, v___x_581_, v___x_580_);
return v___x_585_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_box(0);
v___x_587_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_588_ = l_Lean_mkConst(v___x_587_, v___x_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(lean_object* v_type_589_, lean_object* v_arity_590_){
_start:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lean_nat_dec_eq(v_arity_590_, v___x_594_);
if (v___x_595_ == 0)
{
switch(lean_obj_tag(v_type_589_))
{
case 7:
{
lean_object* v_body_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_body_596_ = lean_ctor_get(v_type_589_, 2);
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_nat_sub(v_arity_590_, v___x_597_);
lean_dec(v_arity_590_);
v_type_589_ = v_body_596_;
v_arity_590_ = v___x_598_;
goto _start;
}
case 4:
{
lean_object* v_declName_600_; 
lean_dec(v_arity_590_);
v_declName_600_ = lean_ctor_get(v_type_589_, 0);
if (lean_obj_tag(v_declName_600_) == 1)
{
lean_object* v_pre_601_; 
v_pre_601_ = lean_ctor_get(v_declName_600_, 0);
if (lean_obj_tag(v_pre_601_) == 0)
{
lean_object* v_str_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_str_602_ = lean_ctor_get(v_declName_600_, 1);
v___x_603_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0));
v___x_604_ = lean_string_dec_eq(v_str_602_, v___x_603_);
if (v___x_604_ == 0)
{
goto v___jp_591_;
}
else
{
lean_object* v___x_605_; 
v___x_605_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4);
return v___x_605_;
}
}
else
{
goto v___jp_591_;
}
}
else
{
goto v___jp_591_;
}
}
default: 
{
lean_dec(v_arity_590_);
goto v___jp_591_;
}
}
}
else
{
lean_dec(v_arity_590_);
lean_inc_ref(v_type_589_);
return v_type_589_;
}
v___jp_591_:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3);
v___x_593_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(v___x_592_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___boxed(lean_object* v_type_606_, lean_object* v_arity_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_606_, v_arity_607_);
lean_dec_ref(v_type_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object* v_type_609_, lean_object* v_arity_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_609_, v_arity_610_);
v___x_615_ = l_Lean_Compiler_LCNF_toImpureType(v___x_614_, v_a_611_, v_a_612_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType___boxed(lean_object* v_type_616_, lean_object* v_arity_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_616_, v_arity_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec_ref(v_type_616_);
return v_res_621_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_box(0);
v___x_626_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1));
v___x_627_ = l_Lean_Expr_const___override(v___x_626_, v___x_625_);
return v___x_627_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_box(0);
v___x_632_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4));
v___x_633_ = l_Lean_Expr_const___override(v___x_632_, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_box(0);
v___x_638_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7));
v___x_639_ = l_Lean_Expr_const___override(v___x_638_, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = lean_box(0);
v___x_644_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10));
v___x_645_ = l_Lean_Expr_const___override(v___x_644_, v___x_643_);
return v___x_645_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_649_ = lean_box(0);
v___x_650_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13));
v___x_651_ = l_Lean_Expr_const___override(v___x_650_, v___x_649_);
return v___x_651_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_655_ = lean_box(0);
v___x_656_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16));
v___x_657_ = l_Lean_Expr_const___override(v___x_656_, v___x_655_);
return v___x_657_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = lean_box(0);
v___x_662_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19));
v___x_663_ = l_Lean_Expr_const___override(v___x_662_, v___x_661_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(lean_object* v_v_664_){
_start:
{
switch(lean_obj_tag(v_v_664_))
{
case 0:
{
lean_object* v_val_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_val_665_ = lean_ctor_get(v_v_664_, 0);
v___x_666_ = lean_cstr_to_nat("4294967296");
v___x_667_ = lean_nat_dec_lt(v_val_665_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
v___x_668_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
return v___x_668_;
}
else
{
lean_object* v___x_669_; 
v___x_669_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
return v___x_669_;
}
}
case 1:
{
lean_object* v___x_670_; 
v___x_670_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
return v___x_670_;
}
case 2:
{
lean_object* v___x_671_; 
v___x_671_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11);
return v___x_671_;
}
case 3:
{
lean_object* v___x_672_; 
v___x_672_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14);
return v___x_672_;
}
case 4:
{
lean_object* v___x_673_; 
v___x_673_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17);
return v___x_673_;
}
case 5:
{
lean_object* v___x_674_; 
v___x_674_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20);
return v___x_674_;
}
default: 
{
lean_object* v___x_675_; 
v___x_675_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___boxed(lean_object* v_v_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_v_676_);
lean_dec_ref(v_v_676_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(lean_object* v_as_678_, size_t v_i_679_, size_t v_stop_680_, lean_object* v_b_681_){
_start:
{
lean_object* v___y_683_; uint8_t v___x_687_; 
v___x_687_ = lean_usize_dec_eq(v_i_679_, v_stop_680_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v_snd_689_; uint8_t v___x_690_; 
v___x_688_ = lean_array_uget_borrowed(v_as_678_, v_i_679_);
v_snd_689_ = lean_ctor_get(v___x_688_, 1);
v___x_690_ = lean_unbox(v_snd_689_);
if (v___x_690_ == 0)
{
v___y_683_ = v_b_681_;
goto v___jp_682_;
}
else
{
lean_object* v_fst_691_; lean_object* v___x_692_; 
v_fst_691_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_fst_691_);
v___x_692_ = lean_array_push(v_b_681_, v_fst_691_);
v___y_683_ = v___x_692_;
goto v___jp_682_;
}
}
else
{
return v_b_681_;
}
v___jp_682_:
{
size_t v___x_684_; size_t v___x_685_; 
v___x_684_ = ((size_t)1ULL);
v___x_685_ = lean_usize_add(v_i_679_, v___x_684_);
v_i_679_ = v___x_685_;
v_b_681_ = v___y_683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4___boxed(lean_object* v_as_693_, lean_object* v_i_694_, lean_object* v_stop_695_, lean_object* v_b_696_){
_start:
{
size_t v_i_boxed_697_; size_t v_stop_boxed_698_; lean_object* v_res_699_; 
v_i_boxed_697_ = lean_unbox_usize(v_i_694_);
lean_dec(v_i_694_);
v_stop_boxed_698_ = lean_unbox_usize(v_stop_695_);
lean_dec(v_stop_695_);
v_res_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v_as_693_, v_i_boxed_697_, v_stop_boxed_698_, v_b_696_);
lean_dec_ref(v_as_693_);
return v_res_699_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0(void){
_start:
{
uint8_t v___x_700_; lean_object* v___x_701_; 
v___x_700_ = 1;
v___x_701_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(lean_object* v_msg_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_709_; lean_object* v_toApplicative_710_; lean_object* v_toFunctor_711_; lean_object* v_toSeq_712_; lean_object* v_toSeqLeft_713_; lean_object* v_toSeqRight_714_; lean_object* v___f_715_; lean_object* v___f_716_; lean_object* v___f_717_; lean_object* v___f_718_; lean_object* v___x_719_; lean_object* v___f_720_; lean_object* v___f_721_; lean_object* v___f_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_toApplicative_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_758_; 
v___x_709_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_710_ = lean_ctor_get(v___x_709_, 0);
v_toFunctor_711_ = lean_ctor_get(v_toApplicative_710_, 0);
v_toSeq_712_ = lean_ctor_get(v_toApplicative_710_, 2);
v_toSeqLeft_713_ = lean_ctor_get(v_toApplicative_710_, 3);
v_toSeqRight_714_ = lean_ctor_get(v_toApplicative_710_, 4);
v___f_715_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_716_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref_n(v_toFunctor_711_, 2);
v___f_717_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_717_, 0, v_toFunctor_711_);
v___f_718_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_718_, 0, v_toFunctor_711_);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___f_717_);
lean_ctor_set(v___x_719_, 1, v___f_718_);
lean_inc(v_toSeqRight_714_);
v___f_720_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_720_, 0, v_toSeqRight_714_);
lean_inc(v_toSeqLeft_713_);
v___f_721_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_721_, 0, v_toSeqLeft_713_);
lean_inc(v_toSeq_712_);
v___f_722_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_722_, 0, v_toSeq_712_);
v___x_723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_723_, 0, v___x_719_);
lean_ctor_set(v___x_723_, 1, v___f_715_);
lean_ctor_set(v___x_723_, 2, v___f_722_);
lean_ctor_set(v___x_723_, 3, v___f_721_);
lean_ctor_set(v___x_723_, 4, v___f_720_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___f_716_);
v___x_725_ = l_StateRefT_x27_instMonad___redArg(v___x_724_);
v_toApplicative_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v___x_725_, 1);
lean_dec(v_unused_759_);
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_758_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_toApplicative_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_758_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_toFunctor_730_; lean_object* v_toSeq_731_; lean_object* v_toSeqLeft_732_; lean_object* v_toSeqRight_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_756_; 
v_toFunctor_730_ = lean_ctor_get(v_toApplicative_726_, 0);
v_toSeq_731_ = lean_ctor_get(v_toApplicative_726_, 2);
v_toSeqLeft_732_ = lean_ctor_get(v_toApplicative_726_, 3);
v_toSeqRight_733_ = lean_ctor_get(v_toApplicative_726_, 4);
v_isSharedCheck_756_ = !lean_is_exclusive(v_toApplicative_726_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v_toApplicative_726_, 1);
lean_dec(v_unused_757_);
v___x_735_ = v_toApplicative_726_;
v_isShared_736_ = v_isSharedCheck_756_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_toSeqRight_733_);
lean_inc(v_toSeqLeft_732_);
lean_inc(v_toSeq_731_);
lean_inc(v_toFunctor_730_);
lean_dec(v_toApplicative_726_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_756_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___f_737_; lean_object* v___f_738_; lean_object* v___f_739_; lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___f_744_; lean_object* v___x_746_; 
v___f_737_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_738_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_730_);
v___f_739_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_739_, 0, v_toFunctor_730_);
v___f_740_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_740_, 0, v_toFunctor_730_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___f_739_);
lean_ctor_set(v___x_741_, 1, v___f_740_);
v___f_742_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_742_, 0, v_toSeqRight_733_);
v___f_743_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_743_, 0, v_toSeqLeft_732_);
v___f_744_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_744_, 0, v_toSeq_731_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 4, v___f_742_);
lean_ctor_set(v___x_735_, 3, v___f_743_);
lean_ctor_set(v___x_735_, 2, v___f_744_);
lean_ctor_set(v___x_735_, 1, v___f_737_);
lean_ctor_set(v___x_735_, 0, v___x_741_);
v___x_746_ = v___x_735_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___f_737_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v___f_744_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v___f_743_);
lean_ctor_set(v_reuseFailAlloc_755_, 4, v___f_742_);
v___x_746_ = v_reuseFailAlloc_755_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_748_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v___f_738_);
lean_ctor_set(v___x_728_, 0, v___x_746_);
v___x_748_ = v___x_728_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___f_738_);
v___x_748_ = v_reuseFailAlloc_754_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_37422__overap_752_; lean_object* v___x_753_; 
v___x_749_ = l_StateRefT_x27_instMonad___redArg(v___x_748_);
v___x_750_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0);
v___x_751_ = l_instInhabitedOfMonad___redArg(v___x_749_, v___x_750_);
v___x_37422__overap_752_ = lean_panic_fn_borrowed(v___x_751_, v_msg_702_);
lean_dec(v___x_751_);
lean_inc(v___y_707_);
lean_inc_ref(v___y_706_);
lean_inc(v___y_705_);
lean_inc_ref(v___y_704_);
lean_inc(v___y_703_);
v___x_753_ = lean_apply_6(v___x_37422__overap_752_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, lean_box(0));
return v___x_753_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(lean_object* v_msg_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v_msg_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
return v_res_767_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0(void){
_start:
{
uint8_t v___x_768_; lean_object* v___x_769_; 
v___x_768_ = 0;
v___x_769_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(lean_object* v_upperBound_770_, lean_object* v_params_771_, lean_object* v___x_772_, lean_object* v_discr_773_, lean_object* v_a_774_, lean_object* v_b_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_a_779_; uint8_t v___x_783_; 
v___x_783_ = lean_nat_dec_lt(v_a_774_, v_upperBound_770_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; 
lean_dec(v_a_774_);
lean_dec(v_discr_773_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v_b_775_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_785_ = lean_box(0);
v___x_786_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0);
v___x_787_ = lean_array_get_borrowed(v___x_786_, v_params_771_, v_a_774_);
v___x_788_ = lean_nat_dec_eq(v_a_774_, v___x_772_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v_fvarId_790_; lean_object* v_subst_791_; lean_object* v_jpParamMask_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_802_; 
v___x_789_ = lean_st_ref_take(v___y_776_);
v_fvarId_790_ = lean_ctor_get(v___x_787_, 0);
v_subst_791_ = lean_ctor_get(v___x_789_, 0);
v_jpParamMask_792_ = lean_ctor_get(v___x_789_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_802_ == 0)
{
v___x_794_ = v___x_789_;
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_jpParamMask_792_);
lean_inc(v_subst_791_);
lean_dec(v___x_789_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_796_ = lean_box(0);
lean_inc(v_fvarId_790_);
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_791_, v_fvarId_790_, v___x_796_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_797_);
v___x_799_ = v___x_794_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_jpParamMask_792_);
v___x_799_ = v_reuseFailAlloc_801_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; 
v___x_800_ = lean_st_ref_set(v___y_776_, v___x_799_);
v_a_779_ = v___x_785_;
goto v___jp_778_;
}
}
}
else
{
lean_object* v___x_803_; lean_object* v_fvarId_804_; lean_object* v_subst_805_; lean_object* v_jpParamMask_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_816_; 
v___x_803_ = lean_st_ref_take(v___y_776_);
v_fvarId_804_ = lean_ctor_get(v___x_787_, 0);
v_subst_805_ = lean_ctor_get(v___x_803_, 0);
v_jpParamMask_806_ = lean_ctor_get(v___x_803_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_816_ == 0)
{
v___x_808_ = v___x_803_;
v_isShared_809_ = v_isSharedCheck_816_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_jpParamMask_806_);
lean_inc(v_subst_805_);
lean_dec(v___x_803_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_816_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
lean_inc(v_discr_773_);
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v_discr_773_);
lean_inc(v_fvarId_804_);
v___x_811_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_805_, v_fvarId_804_, v___x_810_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_811_);
v___x_813_ = v___x_808_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_jpParamMask_806_);
v___x_813_ = v_reuseFailAlloc_815_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; 
v___x_814_ = lean_st_ref_set(v___y_776_, v___x_813_);
v_a_779_ = v___x_785_;
goto v___jp_778_;
}
}
}
}
v___jp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_add(v_a_774_, v___x_780_);
lean_dec(v_a_774_);
v_a_774_ = v___x_781_;
v_b_775_ = v_a_779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(lean_object* v_upperBound_817_, lean_object* v_params_818_, lean_object* v___x_819_, lean_object* v_discr_820_, lean_object* v_a_821_, lean_object* v_b_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_817_, v_params_818_, v___x_819_, v_discr_820_, v_a_821_, v_b_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec(v___x_819_);
lean_dec_ref(v_params_818_);
lean_dec(v_upperBound_817_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(size_t v_sz_826_, size_t v_i_827_, lean_object* v_bs_828_){
_start:
{
uint8_t v___x_829_; 
v___x_829_ = lean_usize_dec_lt(v_i_827_, v_sz_826_);
if (v___x_829_ == 0)
{
return v_bs_828_;
}
else
{
lean_object* v_v_830_; lean_object* v_type_831_; lean_object* v___x_832_; lean_object* v_bs_x27_833_; uint8_t v___y_835_; uint8_t v___x_841_; 
v_v_830_ = lean_array_uget_borrowed(v_bs_828_, v_i_827_);
v_type_831_ = lean_ctor_get(v_v_830_, 2);
lean_inc_ref(v_type_831_);
v___x_832_ = lean_unsigned_to_nat(0u);
v_bs_x27_833_ = lean_array_uset(v_bs_828_, v_i_827_, v___x_832_);
v___x_841_ = l_Lean_Expr_isVoid(v_type_831_);
if (v___x_841_ == 0)
{
uint8_t v___x_842_; uint8_t v___x_843_; 
v___x_842_ = l_Lean_Expr_isErased(v_type_831_);
lean_dec_ref(v_type_831_);
v___x_843_ = lean_bool_not(v___x_842_);
v___y_835_ = v___x_843_;
goto v___jp_834_;
}
else
{
uint8_t v___x_844_; 
lean_dec_ref(v_type_831_);
v___x_844_ = lean_bool_not(v___x_841_);
v___y_835_ = v___x_844_;
goto v___jp_834_;
}
v___jp_834_:
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_836_ = ((size_t)1ULL);
v___x_837_ = lean_usize_add(v_i_827_, v___x_836_);
v___x_838_ = lean_box(v___y_835_);
v___x_839_ = lean_array_uset(v_bs_x27_833_, v_i_827_, v___x_838_);
v_i_827_ = v___x_837_;
v_bs_828_ = v___x_839_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object* v_sz_845_, lean_object* v_i_846_, lean_object* v_bs_847_){
_start:
{
size_t v_sz_boxed_848_; size_t v_i_boxed_849_; lean_object* v_res_850_; 
v_sz_boxed_848_ = lean_unbox_usize(v_sz_845_);
lean_dec(v_sz_845_);
v_i_boxed_849_ = lean_unbox_usize(v_i_846_);
lean_dec(v_i_846_);
v_res_850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_boxed_848_, v_i_boxed_849_, v_bs_847_);
return v_res_850_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_851_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
lean_ctor_set(v___x_856_, 2, v___x_855_);
lean_ctor_set(v___x_856_, 3, v___x_855_);
lean_ctor_set(v___x_856_, 4, v___x_854_);
lean_ctor_set(v___x_856_, 5, v___x_854_);
lean_ctor_set(v___x_856_, 6, v___x_854_);
lean_ctor_set(v___x_856_, 7, v___x_854_);
lean_ctor_set(v___x_856_, 8, v___x_854_);
lean_ctor_set(v___x_856_, 9, v___x_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(lean_object* v_msg_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_options_863_; lean_object* v_ref_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_options_863_ = lean_ctor_get(v___y_860_, 2);
v_ref_864_ = lean_ctor_get(v___y_860_, 5);
v___x_865_ = lean_st_ref_get(v___y_861_);
v___x_866_ = lean_st_ref_get(v___y_859_);
v___x_867_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_858_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_890_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_890_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_890_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_890_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v_env_872_; lean_object* v_lctx_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_888_; 
v_env_872_ = lean_ctor_get(v___x_865_, 0);
lean_inc_ref(v_env_872_);
lean_dec(v___x_865_);
v_lctx_873_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v___x_866_, 1);
lean_dec(v_unused_889_);
v___x_875_ = v___x_866_;
v_isShared_876_ = v_isSharedCheck_888_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_lctx_873_);
lean_dec(v___x_866_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_888_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
uint8_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_877_ = lean_unbox(v_a_868_);
lean_dec(v_a_868_);
v___x_878_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_873_, v___x_877_);
lean_dec_ref(v_lctx_873_);
v___x_879_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2);
lean_inc_ref(v_options_863_);
v___x_880_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_880_, 0, v_env_872_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
lean_ctor_set(v___x_880_, 2, v___x_878_);
lean_ctor_set(v___x_880_, 3, v_options_863_);
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 3);
lean_ctor_set(v___x_875_, 1, v_msg_857_);
lean_ctor_set(v___x_875_, 0, v___x_880_);
v___x_882_ = v___x_875_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_msg_857_);
v___x_882_ = v_reuseFailAlloc_887_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; lean_object* v___x_885_; 
lean_inc(v_ref_864_);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v_ref_864_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 1);
lean_ctor_set(v___x_870_, 0, v___x_883_);
v___x_885_ = v___x_870_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec(v___x_866_);
lean_dec(v___x_865_);
lean_dec_ref(v_msg_857_);
v_a_891_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_867_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_867_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(lean_object* v_msg_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(size_t v_sz_906_, size_t v_i_907_, lean_object* v_bs_908_, lean_object* v___y_909_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = lean_usize_dec_lt(v_i_907_, v_sz_906_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v_bs_908_);
return v___x_912_;
}
else
{
lean_object* v_v_913_; lean_object* v___x_914_; 
v_v_913_ = lean_array_uget_borrowed(v_bs_908_, v_i_907_);
lean_inc(v_v_913_);
v___x_914_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_v_913_, v___y_909_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; lean_object* v_bs_x27_917_; size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
v___x_916_ = lean_unsigned_to_nat(0u);
v_bs_x27_917_ = lean_array_uset(v_bs_908_, v_i_907_, v___x_916_);
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_add(v_i_907_, v___x_918_);
v___x_920_ = lean_array_uset(v_bs_x27_917_, v_i_907_, v_a_915_);
v_i_907_ = v___x_919_;
v_bs_908_ = v___x_920_;
goto _start;
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec_ref(v_bs_908_);
v_a_922_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_914_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_914_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg___boxed(lean_object* v_sz_930_, lean_object* v_i_931_, lean_object* v_bs_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
size_t v_sz_boxed_935_; size_t v_i_boxed_936_; lean_object* v_res_937_; 
v_sz_boxed_935_ = lean_unbox_usize(v_sz_930_);
lean_dec(v_sz_930_);
v_i_boxed_936_ = lean_unbox_usize(v_i_931_);
lean_dec(v_i_931_);
v_res_937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_boxed_935_, v_i_boxed_936_, v_bs_932_, v___y_933_);
lean_dec(v___y_933_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(lean_object* v_upperBound_938_, lean_object* v_fieldInfo_939_, lean_object* v___x_940_, lean_object* v_a_941_, lean_object* v_b_942_){
_start:
{
lean_object* v_a_945_; uint8_t v___x_949_; 
v___x_949_ = lean_nat_dec_lt(v_a_941_, v_upperBound_938_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
lean_dec(v_a_941_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_b_942_);
return v___x_950_;
}
else
{
lean_object* v___x_951_; 
v___x_951_ = lean_array_fget_borrowed(v_fieldInfo_939_, v_a_941_);
switch(lean_obj_tag(v___x_951_))
{
case 1:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = lean_box(0);
v___x_953_ = lean_array_get_borrowed(v___x_952_, v___x_940_, v_a_941_);
lean_inc(v___x_953_);
v___x_954_ = lean_array_push(v_b_942_, v___x_953_);
v_a_945_ = v___x_954_;
goto v___jp_944_;
}
case 2:
{
v_a_945_ = v_b_942_;
goto v___jp_944_;
}
case 3:
{
v_a_945_ = v_b_942_;
goto v___jp_944_;
}
default: 
{
v_a_945_ = v_b_942_;
goto v___jp_944_;
}
}
}
v___jp_944_:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_unsigned_to_nat(1u);
v___x_947_ = lean_nat_add(v_a_941_, v___x_946_);
lean_dec(v_a_941_);
v_a_941_ = v___x_947_;
v_b_942_ = v_a_945_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(lean_object* v_upperBound_955_, lean_object* v_fieldInfo_956_, lean_object* v___x_957_, lean_object* v_a_958_, lean_object* v_b_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_955_, v_fieldInfo_956_, v___x_957_, v_a_958_, v_b_959_);
lean_dec_ref(v___x_957_);
lean_dec_ref(v_fieldInfo_956_);
lean_dec(v_upperBound_955_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object* v_as_962_, size_t v_i_963_, size_t v_stop_964_, lean_object* v_b_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_a_969_; uint8_t v___x_973_; 
v___x_973_ = lean_usize_dec_eq(v_i_963_, v_stop_964_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v_snd_975_; uint8_t v___x_976_; 
v___x_974_ = lean_array_uget_borrowed(v_as_962_, v_i_963_);
v_snd_975_ = lean_ctor_get(v___x_974_, 1);
v___x_976_ = lean_unbox(v_snd_975_);
if (v___x_976_ == 0)
{
v_a_969_ = v_b_965_;
goto v___jp_968_;
}
else
{
lean_object* v_fst_977_; lean_object* v___x_978_; 
v_fst_977_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_fst_977_);
v___x_978_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_fst_977_, v___y_966_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = lean_array_push(v_b_965_, v_a_979_);
v_a_969_ = v___x_980_;
goto v___jp_968_;
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v_b_965_);
v_a_981_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_978_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_978_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
else
{
lean_object* v___x_989_; 
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v_b_965_);
return v___x_989_;
}
v___jp_968_:
{
size_t v___x_970_; size_t v___x_971_; 
v___x_970_ = ((size_t)1ULL);
v___x_971_ = lean_usize_add(v_i_963_, v___x_970_);
v_i_963_ = v___x_971_;
v_b_965_ = v_a_969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object* v_as_990_, lean_object* v_i_991_, lean_object* v_stop_992_, lean_object* v_b_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
size_t v_i_boxed_996_; size_t v_stop_boxed_997_; lean_object* v_res_998_; 
v_i_boxed_996_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_stop_boxed_997_ = lean_unbox_usize(v_stop_992_);
lean_dec(v_stop_992_);
v_res_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_990_, v_i_boxed_996_, v_stop_boxed_997_, v_b_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v_as_990_);
return v_res_998_;
}
}
static lean_object* _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0(void){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Array_instInhabited(lean_box(0));
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(lean_object* v_msg_1000_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_obj_once(&l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0, &l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0_once, _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0);
v___x_1002_ = lean_panic_fn_borrowed(v___x_1001_, v_msg_1000_);
return v___x_1002_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1006_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2));
v___x_1007_ = lean_unsigned_to_nat(11u);
v___x_1008_ = lean_unsigned_to_nat(163u);
v___x_1009_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1));
v___x_1010_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0));
v___x_1011_ = l_mkPanicMessageWithDecl(v___x_1010_, v___x_1009_, v___x_1008_, v___x_1007_, v___x_1006_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(lean_object* v_a_1012_, lean_object* v_x_1013_){
_start:
{
if (lean_obj_tag(v_x_1013_) == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3);
v___x_1015_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(v___x_1014_);
return v___x_1015_;
}
else
{
lean_object* v_key_1016_; lean_object* v_value_1017_; lean_object* v_tail_1018_; uint8_t v___x_1019_; 
v_key_1016_ = lean_ctor_get(v_x_1013_, 0);
v_value_1017_ = lean_ctor_get(v_x_1013_, 1);
v_tail_1018_ = lean_ctor_get(v_x_1013_, 2);
v___x_1019_ = l_Lean_instBEqFVarId_beq(v_key_1016_, v_a_1012_);
if (v___x_1019_ == 0)
{
v_x_1013_ = v_tail_1018_;
goto _start;
}
else
{
lean_inc(v_value_1017_);
return v_value_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___boxed(lean_object* v_a_1021_, lean_object* v_x_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_a_1021_, v_x_1022_);
lean_dec(v_x_1022_);
lean_dec(v_a_1021_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(lean_object* v_m_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_buckets_1026_; lean_object* v___x_1027_; uint64_t v___x_1028_; uint64_t v___x_1029_; uint64_t v___x_1030_; uint64_t v_fold_1031_; uint64_t v___x_1032_; uint64_t v___x_1033_; uint64_t v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_buckets_1026_ = lean_ctor_get(v_m_1024_, 1);
v___x_1027_ = lean_array_get_size(v_buckets_1026_);
v___x_1028_ = l_Lean_instHashableFVarId_hash(v_a_1025_);
v___x_1029_ = 32ULL;
v___x_1030_ = lean_uint64_shift_right(v___x_1028_, v___x_1029_);
v_fold_1031_ = lean_uint64_xor(v___x_1028_, v___x_1030_);
v___x_1032_ = 16ULL;
v___x_1033_ = lean_uint64_shift_right(v_fold_1031_, v___x_1032_);
v___x_1034_ = lean_uint64_xor(v_fold_1031_, v___x_1033_);
v___x_1035_ = lean_uint64_to_usize(v___x_1034_);
v___x_1036_ = lean_usize_of_nat(v___x_1027_);
v___x_1037_ = ((size_t)1ULL);
v___x_1038_ = lean_usize_sub(v___x_1036_, v___x_1037_);
v___x_1039_ = lean_usize_land(v___x_1035_, v___x_1038_);
v___x_1040_ = lean_array_uget_borrowed(v_buckets_1026_, v___x_1039_);
v___x_1041_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_a_1025_, v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(lean_object* v_m_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_m_1042_, v_a_1043_);
lean_dec(v_a_1043_);
lean_dec_ref(v_m_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(size_t v_sz_1045_, size_t v_i_1046_, lean_object* v_bs_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
uint8_t v___x_1053_; 
v___x_1053_ = lean_usize_dec_lt(v_i_1046_, v_sz_1045_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_bs_1047_);
return v___x_1054_;
}
else
{
lean_object* v_v_1055_; lean_object* v___x_1056_; 
v_v_1055_ = lean_array_uget_borrowed(v_bs_1047_, v_i_1046_);
lean_inc(v_v_1055_);
v___x_1056_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_v_1055_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1058_; lean_object* v_bs_x27_1059_; size_t v___x_1060_; size_t v___x_1061_; lean_object* v___x_1062_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___x_1058_ = lean_unsigned_to_nat(0u);
v_bs_x27_1059_ = lean_array_uset(v_bs_1047_, v_i_1046_, v___x_1058_);
v___x_1060_ = ((size_t)1ULL);
v___x_1061_ = lean_usize_add(v_i_1046_, v___x_1060_);
v___x_1062_ = lean_array_uset(v_bs_x27_1059_, v_i_1046_, v_a_1057_);
v_i_1046_ = v___x_1061_;
v_bs_1047_ = v___x_1062_;
goto _start;
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec_ref(v_bs_1047_);
v_a_1064_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1056_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1056_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(lean_object* v_sz_1072_, lean_object* v_i_1073_, lean_object* v_bs_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
size_t v_sz_boxed_1080_; size_t v_i_boxed_1081_; lean_object* v_res_1082_; 
v_sz_boxed_1080_ = lean_unbox_usize(v_sz_1072_);
lean_dec(v_sz_1072_);
v_i_boxed_1081_ = lean_unbox_usize(v_i_1073_);
lean_dec(v_i_1073_);
v_res_1082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_boxed_1080_, v_i_boxed_1081_, v_bs_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec(v___y_1075_);
return v_res_1082_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1085_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1));
v___x_1086_ = lean_unsigned_to_nat(12u);
v___x_1087_ = lean_unsigned_to_nat(116u);
v___x_1088_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1089_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1090_ = l_mkPanicMessageWithDecl(v___x_1089_, v___x_1088_, v___x_1087_, v___x_1086_, v___x_1085_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(lean_object* v_k_1091_, lean_object* v_decl_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v___x_1099_; lean_object* v_lctx_1100_; lean_object* v_nextIdx_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1121_; 
v___x_1099_ = lean_st_ref_take(v_a_1095_);
v_lctx_1100_ = lean_ctor_get(v___x_1099_, 0);
v_nextIdx_1101_ = lean_ctor_get(v___x_1099_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1103_ = v___x_1099_;
v_isShared_1104_ = v_isSharedCheck_1121_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_nextIdx_1101_);
lean_inc(v_lctx_1100_);
lean_dec(v___x_1099_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1121_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1105_ = 1;
lean_inc_ref(v_decl_1092_);
v___x_1106_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1105_, v_lctx_1100_, v_decl_1092_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1106_);
v___x_1108_ = v___x_1103_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_nextIdx_1101_);
v___x_1108_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_st_ref_set(v_a_1095_, v___x_1108_);
v___x_1110_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1091_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1119_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_decl_1092_);
lean_ctor_set(v___x_1115_, 1, v_a_1111_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1115_);
v___x_1117_ = v___x_1113_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
else
{
lean_dec_ref(v_decl_1092_);
return v___x_1110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(lean_object* v_k_1122_, lean_object* v_fvarId_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v___x_1130_; lean_object* v_subst_1131_; lean_object* v_jpParamMask_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1143_; 
v___x_1130_ = lean_st_ref_take(v_a_1124_);
v_subst_1131_ = lean_ctor_get(v___x_1130_, 0);
v_jpParamMask_1132_ = lean_ctor_get(v___x_1130_, 1);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1134_ = v___x_1130_;
v_isShared_1135_ = v_isSharedCheck_1143_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_jpParamMask_1132_);
lean_inc(v_subst_1131_);
lean_dec(v___x_1130_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1143_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1136_ = lean_box(0);
v___x_1137_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1131_, v_fvarId_1123_, v___x_1136_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1137_);
v___x_1139_ = v___x_1134_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_jpParamMask_1132_);
v___x_1139_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_st_ref_set(v_a_1124_, v___x_1139_);
v___x_1141_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1122_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
return v___x_1141_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(lean_object* v_decl_1145_, lean_object* v_k_1146_, lean_object* v_name_1147_, lean_object* v_numParams_1148_, lean_object* v_args_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_fvarId_1156_; lean_object* v_binderName_1157_; lean_object* v_type_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1220_; 
v_fvarId_1156_ = lean_ctor_get(v_decl_1145_, 0);
v_binderName_1157_ = lean_ctor_get(v_decl_1145_, 1);
v_type_1158_ = lean_ctor_get(v_decl_1145_, 2);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_decl_1145_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v_decl_1145_, 3);
lean_dec(v_unused_1221_);
v___x_1160_ = v_decl_1145_;
v_isShared_1161_ = v_isSharedCheck_1220_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_type_1158_);
lean_inc(v_binderName_1157_);
lean_inc(v_fvarId_1156_);
lean_dec(v_decl_1145_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1220_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1158_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1148_);
v___x_1165_ = l_Array_extract___redArg(v_args_1149_, v___x_1164_, v_numParams_1148_);
v___x_1166_ = 1;
v___x_1167_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0));
lean_inc(v_binderName_1157_);
v___x_1168_ = l_Lean_Name_str___override(v_binderName_1157_, v___x_1167_);
v___x_1169_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1170_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1170_, 0, v_name_1147_);
lean_ctor_set(v___x_1170_, 1, v___x_1165_);
v___x_1171_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1166_, v___x_1168_, v___x_1169_, v___x_1170_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v_fvarId_1173_; lean_object* v___x_1174_; lean_object* v_lctx_1175_; lean_object* v_nextIdx_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1203_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1171_, 1);
v_fvarId_1173_ = lean_ctor_get(v_a_1172_, 0);
v___x_1174_ = lean_st_ref_take(v_a_1152_);
v_lctx_1175_ = lean_ctor_get(v___x_1174_, 0);
v_nextIdx_1176_ = lean_ctor_get(v___x_1174_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1178_ = v___x_1174_;
v_isShared_1179_ = v_isSharedCheck_1203_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_nextIdx_1176_);
lean_inc(v_lctx_1175_);
lean_dec(v___x_1174_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1203_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1180_ = lean_array_get_size(v_args_1149_);
v___x_1181_ = l_Array_extract___redArg(v_args_1149_, v_numParams_1148_, v___x_1180_);
lean_inc(v_fvarId_1173_);
v___x_1182_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1182_, 0, v_fvarId_1173_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1163_);
lean_dec(v_a_1163_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 3, v___x_1182_);
lean_ctor_set(v___x_1160_, 2, v___x_1183_);
v___x_1185_ = v___x_1160_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_fvarId_1156_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_binderName_1157_);
lean_ctor_set(v_reuseFailAlloc_1202_, 2, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1202_, 3, v___x_1182_);
v___x_1185_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
lean_inc_ref(v___x_1185_);
v___x_1186_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1166_, v_lctx_1175_, v___x_1185_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1186_);
v___x_1188_ = v___x_1178_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_nextIdx_1176_);
v___x_1188_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_st_ref_set(v_a_1152_, v___x_1188_);
v___x_1190_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1146_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1200_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1185_);
lean_ctor_set(v___x_1195_, 1, v_a_1191_);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v_a_1172_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1196_);
v___x_1198_ = v___x_1193_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_dec_ref(v___x_1185_);
lean_dec(v_a_1172_);
return v___x_1190_;
}
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v_a_1163_);
lean_del_object(v___x_1160_);
lean_dec(v_binderName_1157_);
lean_dec(v_fvarId_1156_);
lean_dec(v_numParams_1148_);
lean_dec_ref(v_k_1146_);
v_a_1204_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1171_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1171_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_del_object(v___x_1160_);
lean_dec(v_binderName_1157_);
lean_dec(v_fvarId_1156_);
lean_dec(v_numParams_1148_);
lean_dec(v_name_1147_);
lean_dec_ref(v_k_1146_);
v_a_1212_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1162_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1162_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(lean_object* v_decl_1222_, lean_object* v_k_1223_, lean_object* v_name_1224_, lean_object* v_args_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_fvarId_1232_; lean_object* v_binderName_1233_; lean_object* v_type_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1253_; 
v_fvarId_1232_ = lean_ctor_get(v_decl_1222_, 0);
v_binderName_1233_ = lean_ctor_get(v_decl_1222_, 1);
v_type_1234_ = lean_ctor_get(v_decl_1222_, 2);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_decl_1222_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; 
v_unused_1254_ = lean_ctor_get(v_decl_1222_, 3);
lean_dec(v_unused_1254_);
v___x_1236_ = v_decl_1222_;
v_isShared_1237_ = v_isSharedCheck_1253_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_type_1234_);
lean_inc(v_binderName_1233_);
lean_inc(v_fvarId_1232_);
lean_dec(v_decl_1222_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1253_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1234_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1240_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_name_1224_);
lean_ctor_set(v___x_1240_, 1, v_args_1225_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 3, v___x_1240_);
lean_ctor_set(v___x_1236_, 2, v_a_1239_);
v___x_1242_ = v___x_1236_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_fvarId_1232_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_binderName_1233_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_a_1239_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; 
v___x_1243_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1223_, v___x_1242_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
return v___x_1243_;
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_del_object(v___x_1236_);
lean_dec(v_binderName_1233_);
lean_dec(v_fvarId_1232_);
lean_dec_ref(v_args_1225_);
lean_dec(v_name_1224_);
lean_dec_ref(v_k_1223_);
v_a_1245_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1238_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1238_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(lean_object* v_decl_1255_, lean_object* v_k_1256_, lean_object* v_name_1257_, lean_object* v_args_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_fvarId_1265_; lean_object* v_binderName_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1276_; 
v_fvarId_1265_ = lean_ctor_get(v_decl_1255_, 0);
v_binderName_1266_ = lean_ctor_get(v_decl_1255_, 1);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_decl_1255_);
if (v_isSharedCheck_1276_ == 0)
{
lean_object* v_unused_1277_; lean_object* v_unused_1278_; 
v_unused_1277_ = lean_ctor_get(v_decl_1255_, 3);
lean_dec(v_unused_1277_);
v_unused_1278_ = lean_ctor_get(v_decl_1255_, 2);
lean_dec(v_unused_1278_);
v___x_1268_ = v_decl_1255_;
v_isShared_1269_ = v_isSharedCheck_1276_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_binderName_1266_);
lean_inc(v_fvarId_1265_);
lean_dec(v_decl_1255_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1276_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1270_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1271_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_1271_, 0, v_name_1257_);
lean_ctor_set(v___x_1271_, 1, v_args_1258_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 3, v___x_1271_);
lean_ctor_set(v___x_1268_, 2, v___x_1270_);
v___x_1273_ = v___x_1268_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_fvarId_1265_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_binderName_1266_);
lean_ctor_set(v_reuseFailAlloc_1275_, 2, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1275_, 3, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; 
v___x_1274_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1256_, v___x_1273_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
return v___x_1274_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(lean_object* v_decl_1279_, lean_object* v_k_1280_, lean_object* v_name_1281_, lean_object* v_numParams_1282_, lean_object* v_args_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_numArgs_1290_; uint8_t v___x_1291_; 
v_numArgs_1290_ = lean_array_get_size(v_args_1283_);
v___x_1291_ = lean_nat_dec_lt(v_numArgs_1290_, v_numParams_1282_);
if (v___x_1291_ == 0)
{
uint8_t v___x_1292_; 
v___x_1292_ = lean_nat_dec_eq(v_numArgs_1290_, v_numParams_1282_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
v___x_1293_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_1279_, v_k_1280_, v_name_1281_, v_numParams_1282_, v_args_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec_ref(v_args_1283_);
return v___x_1293_;
}
else
{
lean_object* v___x_1294_; 
lean_dec(v_numParams_1282_);
v___x_1294_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1279_, v_k_1280_, v_name_1281_, v_args_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
return v___x_1294_;
}
}
else
{
lean_object* v___x_1295_; 
lean_dec(v_numParams_1282_);
v___x_1295_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_1279_, v_k_1280_, v_name_1281_, v_args_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
return v___x_1295_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1297_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3));
v___x_1298_ = lean_unsigned_to_nat(14u);
v___x_1299_ = lean_unsigned_to_nat(185u);
v___x_1300_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1301_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1302_ = l_mkPanicMessageWithDecl(v___x_1301_, v___x_1300_, v___x_1299_, v___x_1298_, v___x_1297_);
return v___x_1302_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
v___x_1312_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(lean_object* v_decl_1319_, lean_object* v_k_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___x_1335_; lean_object* v_fvarId_1336_; lean_object* v_binderName_1337_; lean_object* v_type_1338_; lean_object* v_value_1339_; lean_object* v_subst_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1792_; 
v___x_1335_ = lean_st_ref_get(v_a_1321_);
v_fvarId_1336_ = lean_ctor_get(v_decl_1319_, 0);
v_binderName_1337_ = lean_ctor_get(v_decl_1319_, 1);
v_type_1338_ = lean_ctor_get(v_decl_1319_, 2);
v_value_1339_ = lean_ctor_get(v_decl_1319_, 3);
v_subst_1340_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v___x_1335_, 1);
lean_dec(v_unused_1793_);
v___x_1342_ = v___x_1335_;
v_isShared_1343_ = v_isSharedCheck_1792_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_subst_1340_);
lean_dec(v___x_1335_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1792_;
goto v_resetjp_1341_;
}
v___jp_1327_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2);
v___x_1334_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1333_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1334_;
}
v_resetjp_1341_:
{
uint8_t v___x_1344_; uint8_t v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = 0;
v___x_1345_ = 1;
lean_inc(v_value_1339_);
v___x_1346_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v___x_1344_, v_subst_1340_, v_value_1339_, v___x_1345_);
lean_dec_ref(v_subst_1340_);
switch(lean_obj_tag(v___x_1346_))
{
case 0:
{
lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1363_; 
lean_inc(v_binderName_1337_);
lean_inc(v_fvarId_1336_);
lean_del_object(v___x_1342_);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_decl_1319_);
if (v_isSharedCheck_1363_ == 0)
{
lean_object* v_unused_1364_; lean_object* v_unused_1365_; lean_object* v_unused_1366_; lean_object* v_unused_1367_; 
v_unused_1364_ = lean_ctor_get(v_decl_1319_, 3);
lean_dec(v_unused_1364_);
v_unused_1365_ = lean_ctor_get(v_decl_1319_, 2);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v_decl_1319_, 1);
lean_dec(v_unused_1366_);
v_unused_1367_ = lean_ctor_get(v_decl_1319_, 0);
lean_dec(v_unused_1367_);
v___x_1348_ = v_decl_1319_;
v_isShared_1349_ = v_isSharedCheck_1363_;
goto v_resetjp_1347_;
}
else
{
lean_dec(v_decl_1319_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1363_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_value_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1362_; 
v_value_1350_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1352_ = v___x_1346_;
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_value_1350_);
lean_dec(v___x_1346_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_value_1350_);
if (v_isShared_1353_ == 0)
{
v___x_1356_ = v___x_1352_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_value_1350_);
v___x_1356_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1358_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 3, v___x_1356_);
lean_ctor_set(v___x_1348_, 2, v___x_1354_);
v___x_1358_ = v___x_1348_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_fvarId_1336_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_binderName_1337_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; 
v___x_1359_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1320_, v___x_1358_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1359_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1368_; 
lean_inc(v_fvarId_1336_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_decl_1319_);
v___x_1368_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1320_, v_fvarId_1336_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1368_;
}
case 2:
{
lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1471_; 
lean_inc(v_binderName_1337_);
lean_inc(v_fvarId_1336_);
lean_del_object(v___x_1342_);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_decl_1319_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; lean_object* v_unused_1473_; lean_object* v_unused_1474_; lean_object* v_unused_1475_; 
v_unused_1472_ = lean_ctor_get(v_decl_1319_, 3);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_decl_1319_, 2);
lean_dec(v_unused_1473_);
v_unused_1474_ = lean_ctor_get(v_decl_1319_, 1);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v_decl_1319_, 0);
lean_dec(v_unused_1475_);
v___x_1370_ = v_decl_1319_;
v_isShared_1371_ = v_isSharedCheck_1471_;
goto v_resetjp_1369_;
}
else
{
lean_dec(v_decl_1319_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1471_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v_typeName_1372_; lean_object* v_idx_1373_; lean_object* v_struct_1374_; lean_object* v___x_1375_; 
v_typeName_1372_ = lean_ctor_get(v___x_1346_, 0);
lean_inc_n(v_typeName_1372_, 2);
v_idx_1373_ = lean_ctor_get(v___x_1346_, 1);
lean_inc(v_idx_1373_);
v_struct_1374_ = lean_ctor_get(v___x_1346_, 2);
lean_inc(v_struct_1374_);
lean_dec_ref_known(v___x_1346_, 3);
v___x_1375_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_1372_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
if (lean_obj_tag(v_a_1376_) == 1)
{
lean_object* v_val_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1413_; 
lean_dec(v_typeName_1372_);
lean_del_object(v___x_1370_);
lean_dec(v_binderName_1337_);
v_val_1377_ = lean_ctor_get(v_a_1376_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_a_1376_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1379_ = v_a_1376_;
v_isShared_1380_ = v_isSharedCheck_1413_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_val_1377_);
lean_dec(v_a_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1413_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v_fieldIdx_1381_; uint8_t v___x_1382_; 
v_fieldIdx_1381_ = lean_ctor_get(v_val_1377_, 2);
lean_inc(v_fieldIdx_1381_);
lean_dec(v_val_1377_);
v___x_1382_ = lean_nat_dec_eq(v_fieldIdx_1381_, v_idx_1373_);
lean_dec(v_idx_1373_);
lean_dec(v_fieldIdx_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; lean_object* v_subst_1384_; lean_object* v_jpParamMask_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1396_; 
lean_del_object(v___x_1379_);
lean_dec(v_struct_1374_);
v___x_1383_ = lean_st_ref_take(v_a_1321_);
v_subst_1384_ = lean_ctor_get(v___x_1383_, 0);
v_jpParamMask_1385_ = lean_ctor_get(v___x_1383_, 1);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1387_ = v___x_1383_;
v_isShared_1388_ = v_isSharedCheck_1396_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_jpParamMask_1385_);
lean_inc(v_subst_1384_);
lean_dec(v___x_1383_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1396_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1384_, v_fvarId_1336_, v___x_1389_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1390_);
v___x_1392_ = v___x_1387_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_jpParamMask_1385_);
v___x_1392_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_st_ref_set(v_a_1321_, v___x_1392_);
v___x_1394_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1394_;
}
}
}
else
{
lean_object* v___x_1397_; lean_object* v_subst_1398_; lean_object* v_jpParamMask_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1412_; 
v___x_1397_ = lean_st_ref_take(v_a_1321_);
v_subst_1398_ = lean_ctor_get(v___x_1397_, 0);
v_jpParamMask_1399_ = lean_ctor_get(v___x_1397_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1401_ = v___x_1397_;
v_isShared_1402_ = v_isSharedCheck_1412_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_jpParamMask_1399_);
lean_inc(v_subst_1398_);
lean_dec(v___x_1397_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1412_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v_struct_1374_);
v___x_1404_ = v___x_1379_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_struct_1374_);
v___x_1404_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1405_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1398_, v_fvarId_1336_, v___x_1404_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1405_);
v___x_1407_ = v___x_1401_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_jpParamMask_1399_);
v___x_1407_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_st_ref_set(v_a_1321_, v___x_1407_);
v___x_1409_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1409_;
}
}
}
}
}
}
else
{
lean_object* v___x_1414_; lean_object* v_subst_1415_; lean_object* v___x_1416_; 
lean_dec(v_a_1376_);
v___x_1414_ = lean_st_ref_get(v_a_1321_);
v_subst_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc_ref(v_subst_1415_);
lean_dec(v___x_1414_);
v___x_1416_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1415_, v_struct_1374_, v___x_1345_);
lean_dec_ref(v_subst_1415_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_fvarId_1417_; lean_object* v___x_1418_; lean_object* v_env_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; 
v_fvarId_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_fvarId_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___x_1418_ = lean_st_ref_get(v_a_1325_);
v_env_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc_ref(v_env_1419_);
lean_dec(v___x_1418_);
v___x_1420_ = 0;
v___x_1421_ = l_Lean_Environment_find_x3f(v_env_1419_, v_typeName_1372_, v___x_1420_);
if (lean_obj_tag(v___x_1421_) == 1)
{
lean_object* v_val_1422_; 
v_val_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_val_1422_);
lean_dec_ref_known(v___x_1421_, 1);
if (lean_obj_tag(v_val_1422_) == 5)
{
lean_object* v_val_1423_; lean_object* v_ctors_1424_; 
v_val_1423_ = lean_ctor_get(v_val_1422_, 0);
lean_inc_ref(v_val_1423_);
lean_dec_ref_known(v_val_1422_, 1);
v_ctors_1424_ = lean_ctor_get(v_val_1423_, 4);
lean_inc(v_ctors_1424_);
lean_dec_ref(v_val_1423_);
if (lean_obj_tag(v_ctors_1424_) == 1)
{
lean_object* v_tail_1425_; 
v_tail_1425_ = lean_ctor_get(v_ctors_1424_, 1);
if (lean_obj_tag(v_tail_1425_) == 0)
{
lean_object* v_head_1426_; lean_object* v___x_1427_; 
v_head_1426_ = lean_ctor_get(v_ctors_1424_, 0);
lean_inc(v_head_1426_);
lean_dec_ref_known(v_ctors_1424_, 2);
v___x_1427_ = l_Lean_Compiler_LCNF_getCtorLayout(v_head_1426_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v_ctorInfo_1429_; lean_object* v_fieldInfo_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v_fst_1434_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1427_, 1);
v_ctorInfo_1429_ = lean_ctor_get(v_a_1428_, 0);
lean_inc_ref(v_ctorInfo_1429_);
v_fieldInfo_1430_ = lean_ctor_get(v_a_1428_, 1);
lean_inc_ref(v_fieldInfo_1430_);
lean_dec(v_a_1428_);
v___x_1431_ = lean_box(0);
v___x_1432_ = lean_array_get(v___x_1431_, v_fieldInfo_1430_, v_idx_1373_);
lean_dec(v_idx_1373_);
lean_dec_ref(v_fieldInfo_1430_);
v___x_1433_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_fvarId_1417_, v_ctorInfo_1429_, v___x_1432_);
lean_dec_ref(v_ctorInfo_1429_);
v_fst_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_fst_1434_);
if (lean_obj_tag(v_fst_1434_) == 1)
{
lean_object* v___x_1435_; 
lean_dec_ref(v___x_1433_);
lean_del_object(v___x_1370_);
lean_dec(v_binderName_1337_);
v___x_1435_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1320_, v_fvarId_1336_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1435_;
}
else
{
lean_object* v_snd_1436_; lean_object* v___x_1438_; 
v_snd_1436_ = lean_ctor_get(v___x_1433_, 1);
lean_inc(v_snd_1436_);
lean_dec_ref(v___x_1433_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 3, v_fst_1434_);
lean_ctor_set(v___x_1370_, 2, v_snd_1436_);
v___x_1438_ = v___x_1370_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_fvarId_1336_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_binderName_1337_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_snd_1436_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_fst_1434_);
v___x_1438_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; 
v___x_1439_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1320_, v___x_1438_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1439_;
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_fvarId_1417_);
lean_dec(v_idx_1373_);
lean_del_object(v___x_1370_);
lean_dec(v_binderName_1337_);
lean_dec(v_fvarId_1336_);
lean_dec_ref(v_k_1320_);
v_a_1441_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1427_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1427_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1424_, 2);
lean_dec(v_fvarId_1417_);
lean_dec(v_idx_1373_);
lean_del_object(v___x_1370_);
lean_dec(v_binderName_1337_);
lean_dec(v_fvarId_1336_);
lean_dec_ref(v_k_1320_);
v___y_1328_ = v_a_1321_;
v___y_1329_ = v_a_1322_;
v___y_1330_ = v_a_1323_;
v___y_1331_ = v_a_1324_;
v___y_1332_ = v_a_1325_;
goto v___jp_1327_;
}
}
else
{
lean_dec(v_ctors_1424_);
lean_dec(v_fvarId_1417_);
lean_dec(v_idx_1373_);
lean_del_object(v___x_1370_);
lean_dec(v_binderName_1337_);
lean_dec(v_fvarId_1336_);
lean_dec_ref(v_k_1320_);
v___y_1328_ = v_a_1321_;
v___y_1329_ = v_a_1322_;
v___y_1330_ = v_a_1323_;
v___y_1331_ = v_a_1324_;
v___y_1332_ = v_a_1325_;
goto v___jp_1327_;
}
}
else
{
lean_dec(v_val_1422_);
lean_dec(v_fvarId_1417_);
lean_dec(v_idx_1373_);
lean_del_object(v___x_1370_);
lean_dec(v_binderName_1337_);
lean_dec(v_fvarId_1336_);
lean_dec_ref(v_k_1320_);
v___y_1328_ = v_a_1321_;
v___y_1329_ = v_a_1322_;
v___y_1330_ = v_a_1323_;
v___y_1331_ = v_a_1324_;
v___y_1332_ = v_a_1325_;
goto v___jp_1327_;
}
}
else
{
lean_dec(v___x_1421_);
lean_dec(v_fvarId_1417_);
lean_dec(v_idx_1373_);
lean_del_object(v___x_1370_);
lean_dec(v_binderName_1337_);
lean_dec(v_fvarId_1336_);
lean_dec_ref(v_k_1320_);
v___y_1328_ = v_a_1321_;
v___y_1329_ = v_a_1322_;
v___y_1330_ = v_a_1323_;
v___y_1331_ = v_a_1324_;
v___y_1332_ = v_a_1325_;
goto v___jp_1327_;
}
}
else
{
lean_object* v___x_1449_; lean_object* v_subst_1450_; lean_object* v_jpParamMask_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_idx_1373_);
lean_dec(v_typeName_1372_);
lean_del_object(v___x_1370_);
lean_dec(v_binderName_1337_);
v___x_1449_ = lean_st_ref_take(v_a_1321_);
v_subst_1450_ = lean_ctor_get(v___x_1449_, 0);
v_jpParamMask_1451_ = lean_ctor_get(v___x_1449_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1453_ = v___x_1449_;
v_isShared_1454_ = v_isSharedCheck_1462_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_jpParamMask_1451_);
lean_inc(v_subst_1450_);
lean_dec(v___x_1449_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1462_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1455_ = lean_box(0);
v___x_1456_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1450_, v_fvarId_1336_, v___x_1455_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1456_);
v___x_1458_ = v___x_1453_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_jpParamMask_1451_);
v___x_1458_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_st_ref_set(v_a_1321_, v___x_1458_);
v___x_1460_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1460_;
}
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_struct_1374_);
lean_dec(v_idx_1373_);
lean_dec(v_typeName_1372_);
lean_del_object(v___x_1370_);
lean_dec(v_binderName_1337_);
lean_dec(v_fvarId_1336_);
lean_dec_ref(v_k_1320_);
v_a_1463_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1375_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1375_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
case 3:
{
lean_object* v_declName_1476_; lean_object* v_args_1477_; size_t v_sz_1478_; size_t v___x_1479_; lean_object* v___x_1480_; 
v_declName_1476_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_declName_1476_);
v_args_1477_ = lean_ctor_get(v___x_1346_, 2);
lean_inc_ref_n(v_args_1477_, 2);
lean_dec_ref_known(v___x_1346_, 3);
v_sz_1478_ = lean_array_size(v_args_1477_);
v___x_1479_ = ((size_t)0ULL);
v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_1478_, v___x_1479_, v_args_1477_, v_a_1321_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1482_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
lean_inc(v_declName_1476_);
v___x_1482_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1476_, v_a_1325_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1482_, 1);
if (lean_obj_tag(v_a_1483_) == 1)
{
lean_object* v_val_1484_; lean_object* v_params_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec_ref(v_args_1477_);
lean_del_object(v___x_1342_);
v_val_1484_ = lean_ctor_get(v_a_1483_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v_a_1483_, 1);
v_params_1485_ = lean_ctor_get(v_val_1484_, 3);
lean_inc_ref(v_params_1485_);
lean_dec(v_val_1484_);
v___x_1486_ = lean_array_get_size(v_params_1485_);
lean_dec_ref(v_params_1485_);
v___x_1487_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1319_, v_k_1320_, v_declName_1476_, v___x_1486_, v_a_1481_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1487_;
}
else
{
lean_object* v___x_1488_; 
lean_dec(v_a_1483_);
lean_inc(v_declName_1476_);
v___x_1488_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1476_, v_a_1325_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
if (lean_obj_tag(v_a_1489_) == 1)
{
lean_object* v_val_1490_; lean_object* v_toSignature_1491_; lean_object* v_params_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_dec_ref(v_args_1477_);
lean_del_object(v___x_1342_);
v_val_1490_ = lean_ctor_get(v_a_1489_, 0);
lean_inc(v_val_1490_);
lean_dec_ref_known(v_a_1489_, 1);
v_toSignature_1491_ = lean_ctor_get(v_val_1490_, 0);
lean_inc_ref(v_toSignature_1491_);
lean_dec(v_val_1490_);
v_params_1492_ = lean_ctor_get(v_toSignature_1491_, 3);
lean_inc_ref(v_params_1492_);
lean_dec_ref(v_toSignature_1491_);
v___x_1493_ = lean_array_get_size(v_params_1492_);
lean_dec_ref(v_params_1492_);
v___x_1494_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1319_, v_k_1320_, v_declName_1476_, v___x_1493_, v_a_1481_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1494_;
}
else
{
lean_object* v___x_1495_; lean_object* v_env_1496_; uint8_t v___x_1497_; lean_object* v___x_1498_; 
lean_dec(v_a_1489_);
v___x_1495_ = lean_st_ref_get(v_a_1325_);
v_env_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc_ref(v_env_1496_);
lean_dec(v___x_1495_);
v___x_1497_ = 0;
lean_inc(v_declName_1476_);
v___x_1498_ = l_Lean_Environment_find_x3f(v_env_1496_, v_declName_1476_, v___x_1497_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_dec(v_a_1481_);
lean_dec_ref(v_args_1477_);
lean_dec(v_declName_1476_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v___x_1499_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4);
v___x_1500_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1499_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1500_;
}
else
{
lean_object* v_val_1501_; 
v_val_1501_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_val_1501_);
lean_dec_ref_known(v___x_1498_, 1);
switch(lean_obj_tag(v_val_1501_))
{
case 0:
{
lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v_a_1481_);
lean_dec_ref(v_args_1477_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_val_1501_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v_val_1501_, 0);
lean_dec(v_unused_1518_);
v___x_1503_ = v_val_1501_;
v_isShared_1504_ = v_isSharedCheck_1517_;
goto v_resetjp_1502_;
}
else
{
lean_dec(v_val_1501_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1517_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1506_ = l_Lean_Name_toString(v_declName_1476_, v___x_1345_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set_tag(v___x_1503_, 3);
lean_ctor_set(v___x_1503_, 0, v___x_1506_);
v___x_1508_ = v___x_1503_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1510_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 5);
lean_ctor_set(v___x_1342_, 1, v___x_1508_);
lean_ctor_set(v___x_1342_, 0, v___x_1505_);
v___x_1510_ = v___x_1342_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1511_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = l_Lean_MessageData_ofFormat(v___x_1512_);
v___x_1514_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1513_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1514_;
}
}
}
}
case 2:
{
lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_a_1481_);
lean_dec_ref(v_args_1477_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_val_1501_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v_val_1501_, 0);
lean_dec(v_unused_1535_);
v___x_1520_ = v_val_1501_;
v_isShared_1521_ = v_isSharedCheck_1534_;
goto v_resetjp_1519_;
}
else
{
lean_dec(v_val_1501_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1534_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1522_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1523_ = l_Lean_Name_toString(v_declName_1476_, v___x_1345_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 3);
lean_ctor_set(v___x_1520_, 0, v___x_1523_);
v___x_1525_ = v___x_1520_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 5);
lean_ctor_set(v___x_1342_, 1, v___x_1525_);
lean_ctor_set(v___x_1342_, 0, v___x_1522_);
v___x_1527_ = v___x_1342_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1528_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = l_Lean_MessageData_ofFormat(v___x_1529_);
v___x_1531_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1530_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1531_;
}
}
}
}
case 4:
{
lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_a_1481_);
lean_dec_ref(v_args_1477_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_val_1501_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; 
v_unused_1552_ = lean_ctor_get(v_val_1501_, 0);
lean_dec(v_unused_1552_);
v___x_1537_ = v_val_1501_;
v_isShared_1538_ = v_isSharedCheck_1551_;
goto v_resetjp_1536_;
}
else
{
lean_dec(v_val_1501_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1551_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1539_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1540_ = l_Lean_Name_toString(v_declName_1476_, v___x_1345_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 3);
lean_ctor_set(v___x_1537_, 0, v___x_1540_);
v___x_1542_ = v___x_1537_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 5);
lean_ctor_set(v___x_1342_, 1, v___x_1542_);
lean_ctor_set(v___x_1342_, 0, v___x_1539_);
v___x_1544_ = v___x_1342_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1545_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = l_Lean_MessageData_ofFormat(v___x_1546_);
v___x_1548_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1547_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1548_;
}
}
}
}
case 5:
{
lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1568_; 
lean_dec(v_a_1481_);
lean_dec_ref(v_args_1477_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_val_1501_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v_val_1501_, 0);
lean_dec(v_unused_1569_);
v___x_1554_ = v_val_1501_;
v_isShared_1555_ = v_isSharedCheck_1568_;
goto v_resetjp_1553_;
}
else
{
lean_dec(v_val_1501_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1568_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1556_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1557_ = l_Lean_Name_toString(v_declName_1476_, v___x_1345_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set_tag(v___x_1554_, 3);
lean_ctor_set(v___x_1554_, 0, v___x_1557_);
v___x_1559_ = v___x_1554_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1561_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 5);
lean_ctor_set(v___x_1342_, 1, v___x_1559_);
lean_ctor_set(v___x_1342_, 0, v___x_1556_);
v___x_1561_ = v___x_1342_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1562_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = l_Lean_MessageData_ofFormat(v___x_1563_);
v___x_1565_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1564_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1565_;
}
}
}
}
case 6:
{
lean_object* v_val_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1705_; 
v_val_1570_ = lean_ctor_get(v_val_1501_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_val_1501_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1572_ = v_val_1501_;
v_isShared_1573_ = v_isSharedCheck_1705_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_val_1570_);
lean_dec(v_val_1501_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1705_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v_induct_1574_; lean_object* v_cidx_1575_; lean_object* v_numParams_1576_; lean_object* v___x_1577_; 
v_induct_1574_ = lean_ctor_get(v_val_1570_, 1);
lean_inc_n(v_induct_1574_, 2);
v_cidx_1575_ = lean_ctor_get(v_val_1570_, 2);
lean_inc(v_cidx_1575_);
v_numParams_1576_ = lean_ctor_get(v_val_1570_, 3);
lean_inc(v_numParams_1576_);
lean_dec_ref(v_val_1570_);
v___x_1577_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_induct_1574_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
if (lean_obj_tag(v_a_1578_) == 1)
{
lean_object* v_val_1579_; lean_object* v___x_1580_; lean_object* v_numParams_1581_; lean_object* v_fieldIdx_1582_; lean_object* v_subst_1583_; lean_object* v_jpParamMask_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1597_; 
lean_inc(v_fvarId_1336_);
lean_dec(v_numParams_1576_);
lean_dec(v_cidx_1575_);
lean_dec(v_induct_1574_);
lean_del_object(v___x_1572_);
lean_dec(v_a_1481_);
lean_dec(v_declName_1476_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_decl_1319_);
v_val_1579_ = lean_ctor_get(v_a_1578_, 0);
lean_inc(v_val_1579_);
lean_dec_ref_known(v_a_1578_, 1);
v___x_1580_ = lean_st_ref_take(v_a_1321_);
v_numParams_1581_ = lean_ctor_get(v_val_1579_, 1);
lean_inc(v_numParams_1581_);
v_fieldIdx_1582_ = lean_ctor_get(v_val_1579_, 2);
lean_inc(v_fieldIdx_1582_);
lean_dec(v_val_1579_);
v_subst_1583_ = lean_ctor_get(v___x_1580_, 0);
v_jpParamMask_1584_ = lean_ctor_get(v___x_1580_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1586_ = v___x_1580_;
v_isShared_1587_ = v_isSharedCheck_1597_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_jpParamMask_1584_);
lean_inc(v_subst_1583_);
lean_dec(v___x_1580_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1597_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1588_ = lean_box(0);
v___x_1589_ = lean_nat_add(v_numParams_1581_, v_fieldIdx_1582_);
lean_dec(v_fieldIdx_1582_);
lean_dec(v_numParams_1581_);
v___x_1590_ = lean_array_get(v___x_1588_, v_args_1477_, v___x_1589_);
lean_dec(v___x_1589_);
lean_dec_ref(v_args_1477_);
v___x_1591_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1583_, v_fvarId_1336_, v___x_1590_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1591_);
v___x_1593_ = v___x_1586_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_jpParamMask_1584_);
v___x_1593_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_st_ref_set(v_a_1321_, v___x_1593_);
v___x_1595_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1595_;
}
}
}
else
{
lean_object* v___x_1598_; 
lean_dec(v_a_1578_);
lean_dec_ref(v_args_1477_);
v___x_1598_ = l_Lean_Compiler_LCNF_nameToImpureType(v_induct_1574_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; uint8_t v___x_1600_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v___x_1600_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_1599_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; 
lean_dec(v_a_1599_);
lean_dec(v_cidx_1575_);
lean_del_object(v___x_1572_);
v___x_1601_ = l_Lean_Compiler_LCNF_getCtorLayout(v_declName_1476_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1664_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1664_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1664_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v_ctorInfo_1606_; lean_object* v_fieldInfo_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1663_; 
v_ctorInfo_1606_ = lean_ctor_get(v_a_1602_, 0);
v_fieldInfo_1607_ = lean_ctor_get(v_a_1602_, 1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_a_1602_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1609_ = v_a_1602_;
v_isShared_1610_ = v_isSharedCheck_1663_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_fieldInfo_1607_);
lean_inc(v_ctorInfo_1606_);
lean_dec(v_a_1602_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1663_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; uint8_t v___x_1616_; 
v___x_1611_ = lean_array_get_size(v_a_1481_);
v___x_1612_ = l_Array_extract___redArg(v_a_1481_, v_numParams_1576_, v___x_1611_);
lean_dec(v_a_1481_);
v___x_1613_ = lean_array_get_size(v___x_1612_);
v___x_1614_ = lean_array_get_size(v_fieldInfo_1607_);
v___x_1615_ = lean_nat_dec_eq(v___x_1613_, v___x_1614_);
v___x_1616_ = lean_bool_not(v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_del_object(v___x_1604_);
v___x_1617_ = lean_unsigned_to_nat(0u);
v___x_1618_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_1619_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1614_, v_fieldInfo_1607_, v___x_1612_, v___x_1617_, v___x_1618_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; lean_object* v_lctx_1622_; lean_object* v_nextIdx_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1650_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v___x_1621_ = lean_st_ref_take(v_a_1323_);
v_lctx_1622_ = lean_ctor_get(v___x_1621_, 0);
v_nextIdx_1623_ = lean_ctor_get(v___x_1621_, 1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1625_ = v___x_1621_;
v_isShared_1626_ = v_isSharedCheck_1650_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_nextIdx_1623_);
lean_inc(v_lctx_1622_);
lean_dec(v___x_1621_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1650_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; uint8_t v___x_1628_; lean_object* v___x_1630_; 
v___x_1627_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_ctorInfo_1606_);
v___x_1628_ = 1;
lean_inc_ref(v_ctorInfo_1606_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set_tag(v___x_1609_, 5);
lean_ctor_set(v___x_1609_, 1, v_a_1620_);
v___x_1630_ = v___x_1609_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_ctorInfo_1606_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_a_1620_);
v___x_1630_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
lean_inc(v_binderName_1337_);
lean_inc(v_fvarId_1336_);
v___x_1631_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1631_, 0, v_fvarId_1336_);
lean_ctor_set(v___x_1631_, 1, v_binderName_1337_);
lean_ctor_set(v___x_1631_, 2, v___x_1627_);
lean_ctor_set(v___x_1631_, 3, v___x_1630_);
lean_inc_ref(v___x_1631_);
v___x_1632_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1628_, v_lctx_1622_, v___x_1631_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1632_);
v___x_1634_ = v___x_1625_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_nextIdx_1623_);
v___x_1634_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_st_ref_set(v_a_1323_, v___x_1634_);
v___x_1636_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_1319_, v_k_1320_, v_ctorInfo_1606_, v_fieldInfo_1607_, v___x_1612_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
lean_dec_ref(v___x_1612_);
lean_dec_ref(v_fieldInfo_1607_);
lean_dec_ref(v_ctorInfo_1606_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1647_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1647_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1647_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v_a_1637_);
lean_ctor_set(v___x_1342_, 0, v___x_1631_);
v___x_1642_ = v___x_1342_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1644_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1642_);
v___x_1644_ = v___x_1639_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1631_, 4);
lean_del_object(v___x_1342_);
return v___x_1636_;
}
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec_ref(v___x_1612_);
lean_del_object(v___x_1609_);
lean_dec_ref(v_fieldInfo_1607_);
lean_dec_ref(v_ctorInfo_1606_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v_a_1651_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1619_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1619_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
lean_dec_ref(v___x_1612_);
lean_del_object(v___x_1609_);
lean_dec_ref(v_fieldInfo_1607_);
lean_dec_ref(v_ctorInfo_1606_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v___x_1659_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1659_);
v___x_1661_ = v___x_1604_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_numParams_1576_);
lean_dec(v_a_1481_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v_a_1665_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1601_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1601_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1684_; 
lean_inc(v_binderName_1337_);
lean_inc(v_fvarId_1336_);
lean_dec(v_numParams_1576_);
lean_dec(v_a_1481_);
lean_dec(v_declName_1476_);
lean_del_object(v___x_1342_);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_decl_1319_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; lean_object* v_unused_1686_; lean_object* v_unused_1687_; lean_object* v_unused_1688_; 
v_unused_1685_ = lean_ctor_get(v_decl_1319_, 3);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_decl_1319_, 2);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_decl_1319_, 1);
lean_dec(v_unused_1687_);
v_unused_1688_ = lean_ctor_get(v_decl_1319_, 0);
lean_dec(v_unused_1688_);
v___x_1674_ = v_decl_1319_;
v_isShared_1675_ = v_isSharedCheck_1684_;
goto v_resetjp_1673_;
}
else
{
lean_dec(v_decl_1319_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1684_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_1599_, v_cidx_1575_);
lean_dec(v_cidx_1575_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1676_);
v___x_1678_ = v___x_1572_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 3, v___x_1678_);
lean_ctor_set(v___x_1674_, 2, v_a_1599_);
v___x_1680_ = v___x_1674_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_fvarId_1336_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_binderName_1337_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_a_1599_);
lean_ctor_set(v_reuseFailAlloc_1682_, 3, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; 
v___x_1681_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1320_, v___x_1680_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1681_;
}
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_numParams_1576_);
lean_dec(v_cidx_1575_);
lean_del_object(v___x_1572_);
lean_dec(v_a_1481_);
lean_dec(v_declName_1476_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v_a_1689_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1598_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1598_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v_numParams_1576_);
lean_dec(v_cidx_1575_);
lean_dec(v_induct_1574_);
lean_del_object(v___x_1572_);
lean_dec(v_a_1481_);
lean_dec_ref(v_args_1477_);
lean_dec(v_declName_1476_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v_a_1697_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1577_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1577_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
case 7:
{
lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1721_; 
lean_dec(v_a_1481_);
lean_dec_ref(v_args_1477_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_val_1501_);
if (v_isSharedCheck_1721_ == 0)
{
lean_object* v_unused_1722_; 
v_unused_1722_ = lean_ctor_get(v_val_1501_, 0);
lean_dec(v_unused_1722_);
v___x_1707_ = v_val_1501_;
v_isShared_1708_ = v_isSharedCheck_1721_;
goto v_resetjp_1706_;
}
else
{
lean_dec(v_val_1501_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1721_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1709_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11));
v___x_1710_ = l_Lean_Name_toString(v_declName_1476_, v___x_1345_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set_tag(v___x_1707_, 3);
lean_ctor_set(v___x_1707_, 0, v___x_1710_);
v___x_1712_ = v___x_1707_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1714_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 5);
lean_ctor_set(v___x_1342_, 1, v___x_1712_);
lean_ctor_set(v___x_1342_, 0, v___x_1709_);
v___x_1714_ = v___x_1342_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1715_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13));
v___x_1716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1714_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = l_Lean_MessageData_ofFormat(v___x_1716_);
v___x_1718_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1717_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1718_;
}
}
}
}
default: 
{
lean_object* v___x_1723_; 
lean_dec(v_val_1501_);
lean_dec_ref(v_args_1477_);
lean_del_object(v___x_1342_);
v___x_1723_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1319_, v_k_1320_, v_declName_1476_, v_a_1481_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1723_;
}
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec(v_a_1481_);
lean_dec_ref(v_args_1477_);
lean_dec(v_declName_1476_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v_a_1724_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1488_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1488_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v_a_1481_);
lean_dec_ref(v_args_1477_);
lean_dec(v_declName_1476_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v_a_1732_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1482_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1482_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref(v_args_1477_);
lean_dec(v_declName_1476_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_decl_1319_);
v_a_1740_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1480_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1480_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
default: 
{
lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1787_; 
lean_inc_ref(v_type_1338_);
lean_inc(v_binderName_1337_);
lean_inc(v_fvarId_1336_);
lean_del_object(v___x_1342_);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_decl_1319_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; lean_object* v_unused_1789_; lean_object* v_unused_1790_; lean_object* v_unused_1791_; 
v_unused_1788_ = lean_ctor_get(v_decl_1319_, 3);
lean_dec(v_unused_1788_);
v_unused_1789_ = lean_ctor_get(v_decl_1319_, 2);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v_decl_1319_, 1);
lean_dec(v_unused_1790_);
v_unused_1791_ = lean_ctor_get(v_decl_1319_, 0);
lean_dec(v_unused_1791_);
v___x_1749_ = v_decl_1319_;
v_isShared_1750_ = v_isSharedCheck_1787_;
goto v_resetjp_1748_;
}
else
{
lean_dec(v_decl_1319_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1787_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v_fvarId_1751_; lean_object* v_args_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1786_; 
v_fvarId_1751_ = lean_ctor_get(v___x_1346_, 0);
v_args_1752_ = lean_ctor_get(v___x_1346_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1754_ = v___x_1346_;
v_isShared_1755_ = v_isSharedCheck_1786_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_args_1752_);
lean_inc(v_fvarId_1751_);
lean_dec(v___x_1346_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1786_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
size_t v_sz_1756_; size_t v___x_1757_; lean_object* v___x_1758_; 
v_sz_1756_ = lean_array_size(v_args_1752_);
v___x_1757_ = ((size_t)0ULL);
v___x_1758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_1756_, v___x_1757_, v_args_1752_, v_a_1321_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1760_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v___x_1760_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1338_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v___x_1762_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1761_);
lean_dec(v_a_1761_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 1, v_a_1759_);
v___x_1764_ = v___x_1754_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_fvarId_1751_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 3, v___x_1764_);
lean_ctor_set(v___x_1749_, 2, v___x_1762_);
v___x_1766_ = v___x_1749_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_fvarId_1336_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_binderName_1337_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1767_; 
v___x_1767_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1320_, v___x_1766_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1767_;
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec(v_a_1759_);
lean_del_object(v___x_1754_);
lean_dec(v_fvarId_1751_);
lean_del_object(v___x_1749_);
lean_dec(v_binderName_1337_);
lean_dec(v_fvarId_1336_);
lean_dec_ref(v_k_1320_);
v_a_1770_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1760_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1760_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_del_object(v___x_1754_);
lean_dec(v_fvarId_1751_);
lean_del_object(v___x_1749_);
lean_dec_ref(v_type_1338_);
lean_dec(v_binderName_1337_);
lean_dec(v_fvarId_1336_);
lean_dec_ref(v_k_1320_);
v_a_1778_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1758_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1758_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
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
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1));
v___x_1797_ = lean_unsigned_to_nat(15u);
v___x_1798_ = lean_unsigned_to_nat(272u);
v___x_1799_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1800_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1801_ = l_mkPanicMessageWithDecl(v___x_1800_, v___x_1799_, v___x_1798_, v___x_1797_, v___x_1796_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1805_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5));
v___x_1806_ = lean_unsigned_to_nat(6u);
v___x_1807_ = lean_unsigned_to_nat(251u);
v___x_1808_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1809_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1810_ = l_mkPanicMessageWithDecl(v___x_1809_, v___x_1808_, v___x_1807_, v___x_1806_, v___x_1805_);
return v___x_1810_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7(void){
_start:
{
uint8_t v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = 0;
v___x_1812_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1811_);
return v___x_1812_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1814_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8));
v___x_1815_ = lean_unsigned_to_nat(6u);
v___x_1816_ = lean_unsigned_to_nat(253u);
v___x_1817_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1818_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1819_ = l_mkPanicMessageWithDecl(v___x_1818_, v___x_1817_, v___x_1816_, v___x_1815_, v___x_1814_);
return v___x_1819_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1821_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10));
v___x_1822_ = lean_unsigned_to_nat(6u);
v___x_1823_ = lean_unsigned_to_nat(254u);
v___x_1824_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1825_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1826_ = l_mkPanicMessageWithDecl(v___x_1825_, v___x_1824_, v___x_1823_, v___x_1822_, v___x_1821_);
return v___x_1826_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1828_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12));
v___x_1829_ = lean_unsigned_to_nat(45u);
v___x_1830_ = lean_unsigned_to_nat(252u);
v___x_1831_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1832_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1833_ = l_mkPanicMessageWithDecl(v___x_1832_, v___x_1831_, v___x_1830_, v___x_1829_, v___x_1828_);
return v___x_1833_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1836_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1));
v___x_1837_ = lean_unsigned_to_nat(18u);
v___x_1838_ = lean_unsigned_to_nat(293u);
v___x_1839_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0));
v___x_1840_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1841_ = l_mkPanicMessageWithDecl(v___x_1840_, v___x_1839_, v___x_1838_, v___x_1837_, v___x_1836_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object* v_discr_1842_, lean_object* v_k_1843_, lean_object* v_ctorInfo_1844_, lean_object* v_params_1845_, lean_object* v_fields_1846_, lean_object* v_i_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1924_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1930_ = lean_array_get_size(v_params_1845_);
v___x_1931_ = lean_nat_dec_lt(v_i_1847_, v___x_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_box(0);
v___y_1924_ = v___x_1932_;
goto v___jp_1923_;
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_array_fget_borrowed(v_params_1845_, v_i_1847_);
lean_inc(v___x_1933_);
v___x_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
v___y_1924_ = v___x_1934_;
goto v___jp_1923_;
}
v___jp_1854_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2);
v___x_1861_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1860_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
return v___x_1861_;
}
v___jp_1862_:
{
if (lean_obj_tag(v___y_1863_) == 0)
{
lean_dec(v_i_1847_);
lean_dec(v_discr_1842_);
if (lean_obj_tag(v___y_1864_) == 0)
{
lean_object* v___x_1865_; 
v___x_1865_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1843_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
return v___x_1865_;
}
else
{
lean_dec(v___y_1864_);
lean_dec_ref(v_k_1843_);
v___y_1855_ = v_a_1848_;
v___y_1856_ = v_a_1849_;
v___y_1857_ = v_a_1850_;
v___y_1858_ = v_a_1851_;
v___y_1859_ = v_a_1852_;
goto v___jp_1854_;
}
}
else
{
if (lean_obj_tag(v___y_1864_) == 1)
{
lean_object* v_val_1866_; lean_object* v_val_1867_; lean_object* v___x_1868_; lean_object* v_fst_1869_; 
v_val_1866_ = lean_ctor_get(v___y_1863_, 0);
lean_inc(v_val_1866_);
lean_dec_ref_known(v___y_1863_, 1);
v_val_1867_ = lean_ctor_get(v___y_1864_, 0);
lean_inc(v_val_1867_);
lean_dec_ref_known(v___y_1864_, 1);
lean_inc(v_discr_1842_);
v___x_1868_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_discr_1842_, v_ctorInfo_1844_, v_val_1867_);
v_fst_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_fst_1869_);
if (lean_obj_tag(v_fst_1869_) == 1)
{
lean_object* v___x_1870_; lean_object* v_fvarId_1871_; lean_object* v_subst_1872_; lean_object* v_jpParamMask_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v___x_1868_);
v___x_1870_ = lean_st_ref_take(v_a_1848_);
v_fvarId_1871_ = lean_ctor_get(v_val_1866_, 0);
lean_inc(v_fvarId_1871_);
lean_dec(v_val_1866_);
v_subst_1872_ = lean_ctor_get(v___x_1870_, 0);
v_jpParamMask_1873_ = lean_ctor_get(v___x_1870_, 1);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1875_ = v___x_1870_;
v_isShared_1876_ = v_isSharedCheck_1886_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_jpParamMask_1873_);
lean_inc(v_subst_1872_);
lean_dec(v___x_1870_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1886_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1877_ = lean_box(0);
v___x_1878_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1872_, v_fvarId_1871_, v___x_1877_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1878_);
v___x_1880_ = v___x_1875_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_jpParamMask_1873_);
v___x_1880_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = lean_st_ref_set(v_a_1848_, v___x_1880_);
v___x_1882_ = lean_unsigned_to_nat(1u);
v___x_1883_ = lean_nat_add(v_i_1847_, v___x_1882_);
lean_dec(v_i_1847_);
v_i_1847_ = v___x_1883_;
goto _start;
}
}
}
else
{
lean_object* v_snd_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1921_; 
v_snd_1887_ = lean_ctor_get(v___x_1868_, 1);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; 
v_unused_1922_ = lean_ctor_get(v___x_1868_, 0);
lean_dec(v_unused_1922_);
v___x_1889_ = v___x_1868_;
v_isShared_1890_ = v_isSharedCheck_1921_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_snd_1887_);
lean_dec(v___x_1868_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1921_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v_fvarId_1892_; lean_object* v_binderName_1893_; lean_object* v_lctx_1894_; lean_object* v_nextIdx_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1920_; 
v___x_1891_ = lean_st_ref_take(v_a_1850_);
v_fvarId_1892_ = lean_ctor_get(v_val_1866_, 0);
lean_inc(v_fvarId_1892_);
v_binderName_1893_ = lean_ctor_get(v_val_1866_, 1);
lean_inc(v_binderName_1893_);
lean_dec(v_val_1866_);
v_lctx_1894_ = lean_ctor_get(v___x_1891_, 0);
v_nextIdx_1895_ = lean_ctor_get(v___x_1891_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1897_ = v___x_1891_;
v_isShared_1898_ = v_isSharedCheck_1920_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_nextIdx_1895_);
lean_inc(v_lctx_1894_);
lean_dec(v___x_1891_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1920_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
uint8_t v___x_1899_; lean_object* v_decl_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1899_ = 1;
v_decl_1900_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_1900_, 0, v_fvarId_1892_);
lean_ctor_set(v_decl_1900_, 1, v_binderName_1893_);
lean_ctor_set(v_decl_1900_, 2, v_snd_1887_);
lean_ctor_set(v_decl_1900_, 3, v_fst_1869_);
lean_inc_ref(v_decl_1900_);
v___x_1901_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1899_, v_lctx_1894_, v_decl_1900_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1901_);
v___x_1903_ = v___x_1897_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_nextIdx_1895_);
v___x_1903_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1904_ = lean_st_ref_set(v_a_1850_, v___x_1903_);
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = lean_nat_add(v_i_1847_, v___x_1905_);
lean_dec(v_i_1847_);
v___x_1907_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_1842_, v_k_1843_, v_ctorInfo_1844_, v_params_1845_, v_fields_1846_, v___x_1906_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1918_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1918_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1918_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 1, v_a_1908_);
lean_ctor_set(v___x_1889_, 0, v_decl_1900_);
v___x_1913_ = v___x_1889_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_decl_1900_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1915_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1913_);
v___x_1915_ = v___x_1910_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
lean_dec_ref_known(v_decl_1900_, 4);
lean_del_object(v___x_1889_);
return v___x_1907_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___y_1863_, 1);
lean_dec(v___y_1864_);
lean_dec(v_i_1847_);
lean_dec_ref(v_k_1843_);
lean_dec(v_discr_1842_);
v___y_1855_ = v_a_1848_;
v___y_1856_ = v_a_1849_;
v___y_1857_ = v_a_1850_;
v___y_1858_ = v_a_1851_;
v___y_1859_ = v_a_1852_;
goto v___jp_1854_;
}
}
}
v___jp_1923_:
{
lean_object* v___x_1925_; uint8_t v___x_1926_; 
v___x_1925_ = lean_array_get_size(v_fields_1846_);
v___x_1926_ = lean_nat_dec_lt(v_i_1847_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_box(0);
v___y_1863_ = v___y_1924_;
v___y_1864_ = v___x_1927_;
goto v___jp_1862_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_array_fget_borrowed(v_fields_1846_, v_i_1847_);
lean_inc(v___x_1928_);
v___x_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
v___y_1863_ = v___y_1924_;
v___y_1864_ = v___x_1929_;
goto v___jp_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(lean_object* v_discr_1935_, lean_object* v_alt_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
if (lean_obj_tag(v_alt_1936_) == 0)
{
lean_object* v_ctorName_1943_; lean_object* v_params_1944_; lean_object* v_code_1945_; lean_object* v___x_1946_; 
v_ctorName_1943_ = lean_ctor_get(v_alt_1936_, 0);
lean_inc(v_ctorName_1943_);
v_params_1944_ = lean_ctor_get(v_alt_1936_, 1);
lean_inc_ref(v_params_1944_);
v_code_1945_ = lean_ctor_get(v_alt_1936_, 2);
lean_inc_ref(v_code_1945_);
lean_dec_ref_known(v_alt_1936_, 3);
v___x_1946_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_1943_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v_ctorInfo_1948_; lean_object* v_fieldInfo_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1974_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
v_ctorInfo_1948_ = lean_ctor_get(v_a_1947_, 0);
v_fieldInfo_1949_ = lean_ctor_get(v_a_1947_, 1);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_a_1947_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1951_ = v_a_1947_;
v_isShared_1952_ = v_isSharedCheck_1974_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_fieldInfo_1949_);
lean_inc(v_ctorInfo_1948_);
lean_dec(v_a_1947_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1974_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_unsigned_to_nat(0u);
v___x_1954_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_1935_, v_code_1945_, v_ctorInfo_1948_, v_params_1944_, v_fieldInfo_1949_, v___x_1953_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
lean_dec_ref(v_fieldInfo_1949_);
lean_dec_ref(v_params_1944_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1965_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set_tag(v___x_1951_, 1);
lean_ctor_set(v___x_1951_, 1, v_a_1955_);
v___x_1960_ = v___x_1951_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_ctorInfo_1948_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1960_);
v___x_1962_ = v___x_1957_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_del_object(v___x_1951_);
lean_dec_ref(v_ctorInfo_1948_);
v_a_1966_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1954_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1954_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v_code_1945_);
lean_dec_ref(v_params_1944_);
lean_dec(v_discr_1935_);
v_a_1975_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1946_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1946_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
else
{
lean_object* v_code_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_discr_1935_);
v_code_1983_ = lean_ctor_get(v_alt_1936_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_alt_1936_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1985_ = v_alt_1936_;
v_isShared_1986_ = v_isSharedCheck_2007_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_code_1983_);
lean_dec(v_alt_1936_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2007_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; 
v___x_1987_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_1983_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1998_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_1998_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1998_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v_a_1988_);
v___x_1993_ = v___x_1985_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1995_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1993_);
v___x_1995_ = v___x_1990_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_del_object(v___x_1985_);
v_a_1999_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1987_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1987_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(lean_object* v_fvarId_2008_, size_t v_sz_2009_, size_t v_i_2010_, lean_object* v_bs_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
uint8_t v___x_2018_; 
v___x_2018_ = lean_usize_dec_lt(v_i_2010_, v_sz_2009_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; 
lean_dec(v_fvarId_2008_);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_bs_2011_);
return v___x_2019_;
}
else
{
lean_object* v_v_2020_; lean_object* v___x_2021_; 
v_v_2020_ = lean_array_uget_borrowed(v_bs_2011_, v_i_2010_);
lean_inc(v_v_2020_);
lean_inc(v_fvarId_2008_);
v___x_2021_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_fvarId_2008_, v_v_2020_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2023_; lean_object* v_bs_x27_2024_; size_t v___x_2025_; size_t v___x_2026_; lean_object* v___x_2027_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = lean_unsigned_to_nat(0u);
v_bs_x27_2024_ = lean_array_uset(v_bs_2011_, v_i_2010_, v___x_2023_);
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_add(v_i_2010_, v___x_2025_);
v___x_2027_ = lean_array_uset(v_bs_x27_2024_, v_i_2010_, v_a_2022_);
v_i_2010_ = v___x_2026_;
v_bs_2011_ = v___x_2027_;
goto _start;
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec_ref(v_bs_2011_);
lean_dec(v_fvarId_2008_);
v_a_2029_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2021_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2021_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(lean_object* v_c_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
switch(lean_obj_tag(v_c_2037_))
{
case 0:
{
lean_object* v_decl_2044_; lean_object* v_k_2045_; lean_object* v___x_2046_; 
v_decl_2044_ = lean_ctor_get(v_c_2037_, 0);
lean_inc_ref(v_decl_2044_);
v_k_2045_ = lean_ctor_get(v_c_2037_, 1);
lean_inc_ref(v_k_2045_);
lean_dec_ref_known(v_c_2037_, 2);
v___x_2046_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2044_, v_k_2045_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
return v___x_2046_;
}
case 1:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec_ref_known(v_c_2037_, 2);
v___x_2047_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2);
v___x_2048_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2047_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
return v___x_2048_;
}
case 2:
{
lean_object* v_decl_2049_; lean_object* v_k_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2142_; 
v_decl_2049_ = lean_ctor_get(v_c_2037_, 0);
v_k_2050_ = lean_ctor_get(v_c_2037_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_c_2037_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2052_ = v_c_2037_;
v_isShared_2053_ = v_isSharedCheck_2142_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_k_2050_);
lean_inc(v_decl_2049_);
lean_dec(v_c_2037_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2142_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v_fvarId_2054_; lean_object* v_binderName_2055_; lean_object* v_params_2056_; lean_object* v_type_2057_; lean_object* v_value_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2141_; 
v_fvarId_2054_ = lean_ctor_get(v_decl_2049_, 0);
v_binderName_2055_ = lean_ctor_get(v_decl_2049_, 1);
v_params_2056_ = lean_ctor_get(v_decl_2049_, 2);
v_type_2057_ = lean_ctor_get(v_decl_2049_, 3);
v_value_2058_ = lean_ctor_get(v_decl_2049_, 4);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_decl_2049_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2060_ = v_decl_2049_;
v_isShared_2061_ = v_isSharedCheck_2141_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_value_2058_);
lean_inc(v_type_2057_);
lean_inc(v_params_2056_);
lean_inc(v_binderName_2055_);
lean_inc(v_fvarId_2054_);
lean_dec(v_decl_2049_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2141_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
size_t v_sz_2062_; size_t v___x_2063_; lean_object* v___x_2064_; 
v_sz_2062_ = lean_array_size(v_params_2056_);
v___x_2063_ = ((size_t)0ULL);
v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2062_, v___x_2063_, v_params_2056_, v_a_2038_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2066_; lean_object* v_subst_2067_; lean_object* v_jpParamMask_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2132_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v___x_2066_ = lean_st_ref_take(v_a_2038_);
v_subst_2067_ = lean_ctor_get(v___x_2066_, 0);
v_jpParamMask_2068_ = lean_ctor_get(v___x_2066_, 1);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2070_ = v___x_2066_;
v_isShared_2071_ = v_isSharedCheck_2132_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_jpParamMask_2068_);
lean_inc(v_subst_2067_);
lean_dec(v___x_2066_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2132_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
size_t v_sz_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2076_; 
v_sz_2072_ = lean_array_size(v_a_2065_);
lean_inc(v_a_2065_);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_2072_, v___x_2063_, v_a_2065_);
lean_inc_ref(v___x_2073_);
lean_inc(v_fvarId_2054_);
v___x_2074_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_jpParamMask_2068_, v_fvarId_2054_, v___x_2073_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2074_);
v___x_2076_ = v___x_2070_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_subst_2067_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2077_; lean_object* v___y_2079_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2077_ = lean_st_ref_set(v_a_2038_, v___x_2076_);
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3));
v___x_2123_ = l_Array_zip___redArg(v_a_2065_, v___x_2073_);
lean_dec_ref(v___x_2073_);
v___x_2124_ = lean_array_get_size(v___x_2123_);
v___x_2125_ = lean_nat_dec_lt(v___x_2121_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_dec_ref(v___x_2123_);
v___y_2079_ = v___x_2122_;
goto v___jp_2078_;
}
else
{
uint8_t v___x_2126_; 
v___x_2126_ = lean_nat_dec_le(v___x_2124_, v___x_2124_);
if (v___x_2126_ == 0)
{
if (v___x_2125_ == 0)
{
lean_dec_ref(v___x_2123_);
v___y_2079_ = v___x_2122_;
goto v___jp_2078_;
}
else
{
size_t v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_usize_of_nat(v___x_2124_);
v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2123_, v___x_2063_, v___x_2127_, v___x_2122_);
lean_dec_ref(v___x_2123_);
v___y_2079_ = v___x_2128_;
goto v___jp_2078_;
}
}
else
{
size_t v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_usize_of_nat(v___x_2124_);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2123_, v___x_2063_, v___x_2129_, v___x_2122_);
lean_dec_ref(v___x_2123_);
v___y_2079_ = v___x_2130_;
goto v___jp_2078_;
}
}
v___jp_2078_:
{
lean_object* v___x_2080_; 
v___x_2080_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_value_2058_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2082_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2080_, 1);
v___x_2082_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2050_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v___x_2084_ = lean_array_get_size(v_a_2065_);
lean_dec(v_a_2065_);
v___x_2085_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2057_, v___x_2084_, v_a_2041_, v_a_2042_);
lean_dec_ref(v_type_2057_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2112_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2112_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2112_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v_lctx_2091_; lean_object* v_nextIdx_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2111_; 
v___x_2090_ = lean_st_ref_take(v_a_2040_);
v_lctx_2091_ = lean_ctor_get(v___x_2090_, 0);
v_nextIdx_2092_ = lean_ctor_get(v___x_2090_, 1);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2094_ = v___x_2090_;
v_isShared_2095_ = v_isSharedCheck_2111_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_nextIdx_2092_);
lean_inc(v_lctx_2091_);
lean_dec(v___x_2090_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2111_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
uint8_t v___x_2096_; lean_object* v___x_2098_; 
v___x_2096_ = 1;
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 4, v_a_2081_);
lean_ctor_set(v___x_2060_, 3, v_a_2086_);
lean_ctor_set(v___x_2060_, 2, v___y_2079_);
v___x_2098_ = v___x_2060_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_fvarId_2054_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_binderName_2055_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v___y_2079_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_a_2086_);
lean_ctor_set(v_reuseFailAlloc_2110_, 4, v_a_2081_);
v___x_2098_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
lean_inc_ref(v___x_2098_);
v___x_2099_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2096_, v_lctx_2091_, v___x_2098_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2099_);
v___x_2101_ = v___x_2094_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_nextIdx_2092_);
v___x_2101_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2102_ = lean_st_ref_set(v_a_2040_, v___x_2101_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 1, v_a_2083_);
lean_ctor_set(v___x_2052_, 0, v___x_2098_);
v___x_2104_ = v___x_2052_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_a_2083_);
v___x_2104_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2104_);
v___x_2106_ = v___x_2088_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec(v_a_2083_);
lean_dec(v_a_2081_);
lean_dec_ref(v___y_2079_);
lean_del_object(v___x_2060_);
lean_dec(v_binderName_2055_);
lean_dec(v_fvarId_2054_);
lean_del_object(v___x_2052_);
v_a_2113_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2085_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2085_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_dec(v_a_2081_);
lean_dec_ref(v___y_2079_);
lean_dec(v_a_2065_);
lean_del_object(v___x_2060_);
lean_dec_ref(v_type_2057_);
lean_dec(v_binderName_2055_);
lean_dec(v_fvarId_2054_);
lean_del_object(v___x_2052_);
return v___x_2082_;
}
}
else
{
lean_dec_ref(v___y_2079_);
lean_dec(v_a_2065_);
lean_del_object(v___x_2060_);
lean_dec_ref(v_type_2057_);
lean_dec(v_binderName_2055_);
lean_dec(v_fvarId_2054_);
lean_del_object(v___x_2052_);
lean_dec_ref(v_k_2050_);
return v___x_2080_;
}
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_del_object(v___x_2060_);
lean_dec_ref(v_value_2058_);
lean_dec_ref(v_type_2057_);
lean_dec(v_binderName_2055_);
lean_dec(v_fvarId_2054_);
lean_del_object(v___x_2052_);
lean_dec_ref(v_k_2050_);
v_a_2133_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2064_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2064_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2143_; lean_object* v_args_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2180_; 
v_fvarId_2143_ = lean_ctor_get(v_c_2037_, 0);
v_args_2144_ = lean_ctor_get(v_c_2037_, 1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_c_2037_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2146_ = v_c_2037_;
v_isShared_2147_ = v_isSharedCheck_2180_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_args_2144_);
lean_inc(v_fvarId_2143_);
lean_dec(v_c_2037_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2180_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v_a_2149_; lean_object* v___y_2155_; lean_object* v___x_2165_; lean_object* v_jpParamMask_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2165_ = lean_st_ref_get(v_a_2038_);
v_jpParamMask_2166_ = lean_ctor_get(v___x_2165_, 1);
lean_inc_ref(v_jpParamMask_2166_);
lean_dec(v___x_2165_);
v___x_2167_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_jpParamMask_2166_, v_fvarId_2143_);
lean_dec_ref(v_jpParamMask_2166_);
v___x_2168_ = lean_unsigned_to_nat(0u);
v___x_2169_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_2170_ = l_Array_zip___redArg(v_args_2144_, v___x_2167_);
lean_dec_ref(v___x_2167_);
lean_dec_ref(v_args_2144_);
v___x_2171_ = lean_array_get_size(v___x_2170_);
v___x_2172_ = lean_nat_dec_lt(v___x_2168_, v___x_2171_);
if (v___x_2172_ == 0)
{
lean_dec_ref(v___x_2170_);
v_a_2149_ = v___x_2169_;
goto v___jp_2148_;
}
else
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_nat_dec_le(v___x_2171_, v___x_2171_);
if (v___x_2173_ == 0)
{
if (v___x_2172_ == 0)
{
lean_dec_ref(v___x_2170_);
v_a_2149_ = v___x_2169_;
goto v___jp_2148_;
}
else
{
size_t v___x_2174_; size_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = ((size_t)0ULL);
v___x_2175_ = lean_usize_of_nat(v___x_2171_);
v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2170_, v___x_2174_, v___x_2175_, v___x_2169_, v_a_2038_);
lean_dec_ref(v___x_2170_);
v___y_2155_ = v___x_2176_;
goto v___jp_2154_;
}
}
else
{
size_t v___x_2177_; size_t v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = ((size_t)0ULL);
v___x_2178_ = lean_usize_of_nat(v___x_2171_);
v___x_2179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2170_, v___x_2177_, v___x_2178_, v___x_2169_, v_a_2038_);
lean_dec_ref(v___x_2170_);
v___y_2155_ = v___x_2179_;
goto v___jp_2154_;
}
}
v___jp_2148_:
{
lean_object* v___x_2151_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 1, v_a_2149_);
v___x_2151_ = v___x_2146_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_fvarId_2143_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_a_2149_);
v___x_2151_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
return v___x_2152_;
}
}
v___jp_2154_:
{
if (lean_obj_tag(v___y_2155_) == 0)
{
lean_object* v_a_2156_; 
v_a_2156_ = lean_ctor_get(v___y_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___y_2155_, 1);
v_a_2149_ = v_a_2156_;
goto v___jp_2148_;
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_del_object(v___x_2146_);
lean_dec(v_fvarId_2143_);
v_a_2157_ = lean_ctor_get(v___y_2155_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___y_2155_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___y_2155_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___y_2155_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
}
case 4:
{
lean_object* v_cases_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2291_; 
v_cases_2181_ = lean_ctor_get(v_c_2037_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_c_2037_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2183_ = v_c_2037_;
v_isShared_2184_ = v_isSharedCheck_2291_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_cases_2181_);
lean_dec(v_c_2037_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2291_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v_typeName_2185_; lean_object* v_resultType_2186_; lean_object* v_discr_2187_; lean_object* v_alts_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2290_; 
v_typeName_2185_ = lean_ctor_get(v_cases_2181_, 0);
v_resultType_2186_ = lean_ctor_get(v_cases_2181_, 1);
v_discr_2187_ = lean_ctor_get(v_cases_2181_, 2);
v_alts_2188_ = lean_ctor_get(v_cases_2181_, 3);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_cases_2181_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2190_ = v_cases_2181_;
v_isShared_2191_ = v_isSharedCheck_2290_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_alts_2188_);
lean_inc(v_discr_2187_);
lean_inc(v_resultType_2186_);
lean_inc(v_typeName_2185_);
lean_dec(v_cases_2181_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2290_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; 
lean_inc(v_typeName_2185_);
v___x_2192_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_2185_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
if (lean_obj_tag(v_a_2193_) == 1)
{
lean_object* v_val_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
lean_del_object(v___x_2190_);
lean_dec_ref(v_resultType_2186_);
lean_dec(v_typeName_2185_);
lean_del_object(v___x_2183_);
v_val_2194_ = lean_ctor_get(v_a_2193_, 0);
lean_inc(v_val_2194_);
lean_dec_ref_known(v_a_2193_, 1);
v___x_2195_ = lean_array_get_size(v_alts_2188_);
v___x_2196_ = lean_unsigned_to_nat(1u);
v___x_2197_ = lean_nat_dec_eq(v___x_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_dec(v_val_2194_);
lean_dec_ref(v_alts_2188_);
lean_dec(v_discr_2187_);
v___x_2198_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6);
v___x_2199_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2198_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
return v___x_2199_;
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = lean_array_get(v___x_2200_, v_alts_2188_, v___x_2201_);
lean_dec_ref(v_alts_2188_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_ctorName_2203_; lean_object* v_params_2204_; lean_object* v_code_2205_; lean_object* v_ctorName_2206_; lean_object* v_fieldIdx_2207_; uint8_t v___x_2208_; 
v_ctorName_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_ctorName_2203_);
v_params_2204_ = lean_ctor_get(v___x_2202_, 1);
lean_inc_ref(v_params_2204_);
v_code_2205_ = lean_ctor_get(v___x_2202_, 2);
lean_inc_ref(v_code_2205_);
lean_dec_ref_known(v___x_2202_, 3);
v_ctorName_2206_ = lean_ctor_get(v_val_2194_, 0);
lean_inc(v_ctorName_2206_);
v_fieldIdx_2207_ = lean_ctor_get(v_val_2194_, 2);
lean_inc(v_fieldIdx_2207_);
lean_dec(v_val_2194_);
v___x_2208_ = lean_name_eq(v_ctorName_2203_, v_ctorName_2206_);
lean_dec(v_ctorName_2206_);
lean_dec(v_ctorName_2203_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_dec(v_fieldIdx_2207_);
lean_dec_ref(v_code_2205_);
lean_dec_ref(v_params_2204_);
lean_dec(v_discr_2187_);
v___x_2209_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9);
v___x_2210_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2209_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
return v___x_2210_;
}
else
{
lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = lean_array_get_size(v_params_2204_);
v___x_2212_ = lean_nat_dec_lt(v_fieldIdx_2207_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec(v_fieldIdx_2207_);
lean_dec_ref(v_code_2205_);
lean_dec_ref(v_params_2204_);
lean_dec(v_discr_2187_);
v___x_2213_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11);
v___x_2214_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2213_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
return v___x_2214_;
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_box(0);
v___x_2216_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v___x_2211_, v_params_2204_, v_fieldIdx_2207_, v_discr_2187_, v___x_2201_, v___x_2215_, v_a_2038_);
lean_dec(v_fieldIdx_2207_);
lean_dec_ref(v_params_2204_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_dec_ref_known(v___x_2216_, 1);
v_c_2037_ = v_code_2205_;
goto _start;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_code_2205_);
v_a_2218_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2216_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2216_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_dec(v___x_2202_);
lean_dec(v_val_2194_);
lean_dec(v_discr_2187_);
v___x_2226_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13);
v___x_2227_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2226_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
return v___x_2227_;
}
}
}
else
{
lean_object* v___x_2228_; lean_object* v_subst_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v_a_2193_);
v___x_2228_ = lean_st_ref_get(v_a_2038_);
v_subst_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc_ref(v_subst_2229_);
lean_dec(v___x_2228_);
v___x_2230_ = 1;
v___x_2231_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2229_, v_discr_2187_, v___x_2230_);
lean_dec_ref(v_subst_2229_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_fvarId_2232_; lean_object* v___x_2233_; 
v_fvarId_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_fvarId_2232_);
lean_dec_ref_known(v___x_2231_, 1);
v___x_2233_ = l_Lean_Compiler_LCNF_toImpureType(v_resultType_2186_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; size_t v_sz_2235_; size_t v___x_2236_; lean_object* v___x_2237_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
v_sz_2235_ = lean_array_size(v_alts_2188_);
v___x_2236_ = ((size_t)0ULL);
lean_inc(v_fvarId_2232_);
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2232_, v_sz_2235_, v___x_2236_, v_alts_2188_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2239_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2237_, 1);
v___x_2239_ = l_Lean_Compiler_LCNF_nameToImpureType(v_typeName_2185_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2255_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2242_ = v___x_2239_;
v_isShared_2243_ = v_isSharedCheck_2255_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2255_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2244_ = l_Lean_Expr_getAppFn(v_a_2240_);
lean_dec(v_a_2240_);
v___x_2245_ = l_Lean_Expr_constName_x21(v___x_2244_);
lean_dec_ref(v___x_2244_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 3, v_a_2238_);
lean_ctor_set(v___x_2190_, 2, v_fvarId_2232_);
lean_ctor_set(v___x_2190_, 1, v_a_2234_);
lean_ctor_set(v___x_2190_, 0, v___x_2245_);
v___x_2247_ = v___x_2190_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_a_2234_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_fvarId_2232_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v_a_2238_);
v___x_2247_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2249_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2247_);
v___x_2249_ = v___x_2183_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2251_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v___x_2249_);
v___x_2251_ = v___x_2242_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v_a_2238_);
lean_dec(v_a_2234_);
lean_dec(v_fvarId_2232_);
lean_del_object(v___x_2190_);
lean_del_object(v___x_2183_);
v_a_2256_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2239_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2239_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_a_2234_);
lean_dec(v_fvarId_2232_);
lean_del_object(v___x_2190_);
lean_dec(v_typeName_2185_);
lean_del_object(v___x_2183_);
v_a_2264_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2237_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2237_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_fvarId_2232_);
lean_del_object(v___x_2190_);
lean_dec_ref(v_alts_2188_);
lean_dec(v_typeName_2185_);
lean_del_object(v___x_2183_);
v_a_2272_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2233_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2233_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
uint8_t v___x_2280_; lean_object* v___x_2281_; 
lean_del_object(v___x_2190_);
lean_dec_ref(v_alts_2188_);
lean_dec_ref(v_resultType_2186_);
lean_dec(v_typeName_2185_);
lean_del_object(v___x_2183_);
v___x_2280_ = 1;
v___x_2281_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2280_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
return v___x_2281_;
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_del_object(v___x_2190_);
lean_dec_ref(v_alts_2188_);
lean_dec(v_discr_2187_);
lean_dec_ref(v_resultType_2186_);
lean_dec(v_typeName_2185_);
lean_del_object(v___x_2183_);
v_a_2282_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2192_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2192_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2313_; 
v_fvarId_2292_ = lean_ctor_get(v_c_2037_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_c_2037_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2294_ = v_c_2037_;
v_isShared_2295_ = v_isSharedCheck_2313_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_fvarId_2292_);
lean_dec(v_c_2037_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2313_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v_subst_2297_; uint8_t v___x_2298_; lean_object* v___x_2299_; 
v___x_2296_ = lean_st_ref_get(v_a_2038_);
v_subst_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc_ref(v_subst_2297_);
lean_dec(v___x_2296_);
v___x_2298_ = 1;
v___x_2299_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2297_, v_fvarId_2292_, v___x_2298_);
lean_dec_ref(v_subst_2297_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_fvarId_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2310_; 
v_fvarId_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2310_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_fvarId_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2310_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v_fvarId_2300_);
v___x_2305_ = v___x_2294_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_fvarId_2300_);
v___x_2305_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2307_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2305_);
v___x_2307_ = v___x_2302_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
uint8_t v___x_2311_; lean_object* v___x_2312_; 
lean_del_object(v___x_2294_);
v___x_2311_ = 1;
v___x_2312_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2311_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
return v___x_2312_;
}
}
}
default: 
{
lean_object* v_type_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2338_; 
v_type_2314_ = lean_ctor_get(v_c_2037_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_c_2037_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2316_ = v_c_2037_;
v_isShared_2317_ = v_isSharedCheck_2338_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_type_2314_);
lean_dec(v_c_2037_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2338_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_Compiler_LCNF_toImpureType(v_type_2314_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2329_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2329_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2329_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v_a_2319_);
v___x_2324_ = v___x_2316_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2326_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2324_);
v___x_2326_ = v___x_2321_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_del_object(v___x_2316_);
v_a_2330_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2318_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2318_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(lean_object* v_decl_2339_, lean_object* v_k_2340_, lean_object* v_ctorInfo_2341_, lean_object* v_fields_2342_, lean_object* v_irArgs_2343_, lean_object* v_i_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v___x_2351_; uint8_t v___x_2352_; 
v___x_2351_ = lean_array_get_size(v_irArgs_2343_);
v___x_2352_ = lean_nat_dec_lt(v_i_2344_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; 
lean_dec(v_i_2344_);
lean_dec_ref(v_decl_2339_);
v___x_2353_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2340_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
return v___x_2353_;
}
else
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_array_fget_borrowed(v_irArgs_2343_, v_i_2344_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_unsigned_to_nat(1u);
v___x_2356_ = lean_nat_add(v_i_2344_, v___x_2355_);
lean_dec(v_i_2344_);
v_i_2344_ = v___x_2356_;
goto _start;
}
else
{
lean_object* v_fvarId_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_fvarId_2358_ = lean_ctor_get(v___x_2354_, 0);
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_array_get_borrowed(v___x_2359_, v_fields_2342_, v_i_2344_);
switch(lean_obj_tag(v___x_2360_))
{
case 1:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_unsigned_to_nat(1u);
v___x_2362_ = lean_nat_add(v_i_2344_, v___x_2361_);
lean_dec(v_i_2344_);
v_i_2344_ = v___x_2362_;
goto _start;
}
case 2:
{
lean_object* v_i_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v_i_2364_ = lean_ctor_get(v___x_2360_, 0);
v___x_2365_ = lean_unsigned_to_nat(1u);
v___x_2366_ = lean_nat_add(v_i_2344_, v___x_2365_);
lean_dec(v_i_2344_);
lean_inc_ref(v_decl_2339_);
v___x_2367_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2339_, v_k_2340_, v_ctorInfo_2341_, v_fields_2342_, v_irArgs_2343_, v___x_2366_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2386_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2386_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2386_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v_fvarId_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2382_; 
v_fvarId_2372_ = lean_ctor_get(v_decl_2339_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_decl_2339_);
if (v_isSharedCheck_2382_ == 0)
{
lean_object* v_unused_2383_; lean_object* v_unused_2384_; lean_object* v_unused_2385_; 
v_unused_2383_ = lean_ctor_get(v_decl_2339_, 3);
lean_dec(v_unused_2383_);
v_unused_2384_ = lean_ctor_get(v_decl_2339_, 2);
lean_dec(v_unused_2384_);
v_unused_2385_ = lean_ctor_get(v_decl_2339_, 1);
lean_dec(v_unused_2385_);
v___x_2374_ = v_decl_2339_;
v_isShared_2375_ = v_isSharedCheck_2382_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_fvarId_2372_);
lean_dec(v_decl_2339_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2382_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
lean_inc(v_fvarId_2358_);
lean_inc(v_i_2364_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set_tag(v___x_2374_, 8);
lean_ctor_set(v___x_2374_, 3, v_a_2368_);
lean_ctor_set(v___x_2374_, 2, v_fvarId_2358_);
lean_ctor_set(v___x_2374_, 1, v_i_2364_);
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_fvarId_2372_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_i_2364_);
lean_ctor_set(v_reuseFailAlloc_2381_, 2, v_fvarId_2358_);
lean_ctor_set(v_reuseFailAlloc_2381_, 3, v_a_2368_);
v___x_2377_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2379_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v___x_2377_);
v___x_2379_ = v___x_2370_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_2339_);
return v___x_2367_;
}
}
case 3:
{
lean_object* v_offset_2387_; lean_object* v_type_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v_offset_2387_ = lean_ctor_get(v___x_2360_, 1);
v_type_2388_ = lean_ctor_get(v___x_2360_, 2);
v___x_2389_ = lean_unsigned_to_nat(1u);
v___x_2390_ = lean_nat_add(v_i_2344_, v___x_2389_);
lean_dec(v_i_2344_);
lean_inc_ref(v_decl_2339_);
v___x_2391_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2339_, v_k_2340_, v_ctorInfo_2341_, v_fields_2342_, v_irArgs_2343_, v___x_2390_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2404_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2404_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2404_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v_fvarId_2396_; lean_object* v_size_2397_; lean_object* v_usize_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2402_; 
v_fvarId_2396_ = lean_ctor_get(v_decl_2339_, 0);
lean_inc(v_fvarId_2396_);
lean_dec_ref(v_decl_2339_);
v_size_2397_ = lean_ctor_get(v_ctorInfo_2341_, 2);
v_usize_2398_ = lean_ctor_get(v_ctorInfo_2341_, 3);
v___x_2399_ = lean_nat_add(v_size_2397_, v_usize_2398_);
lean_inc_ref(v_type_2388_);
lean_inc(v_fvarId_2358_);
lean_inc(v_offset_2387_);
v___x_2400_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_2400_, 0, v_fvarId_2396_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
lean_ctor_set(v___x_2400_, 2, v_offset_2387_);
lean_ctor_set(v___x_2400_, 3, v_fvarId_2358_);
lean_ctor_set(v___x_2400_, 4, v_type_2388_);
lean_ctor_set(v___x_2400_, 5, v_a_2392_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v___x_2400_);
v___x_2402_ = v___x_2394_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
else
{
lean_dec_ref(v_decl_2339_);
return v___x_2391_;
}
}
default: 
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = lean_nat_add(v_i_2344_, v___x_2405_);
lean_dec(v_i_2344_);
v_i_2344_ = v___x_2406_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(lean_object* v_decl_2408_, lean_object* v_k_2409_, lean_object* v_ctorInfo_2410_, lean_object* v_fields_2411_, lean_object* v_irArgs_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_unsigned_to_nat(0u);
v___x_2420_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2408_, v_k_2409_, v_ctorInfo_2410_, v_fields_2411_, v_irArgs_2412_, v___x_2419_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(lean_object* v_decl_2421_, lean_object* v_k_2422_, lean_object* v_ctorInfo_2423_, lean_object* v_fields_2424_, lean_object* v_irArgs_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_2421_, v_k_2422_, v_ctorInfo_2423_, v_fields_2424_, v_irArgs_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec_ref(v_irArgs_2425_);
lean_dec_ref(v_fields_2424_);
lean_dec_ref(v_ctorInfo_2423_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(lean_object* v_decl_2433_, lean_object* v_k_2434_, lean_object* v_name_2435_, lean_object* v_args_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_2433_, v_k_2434_, v_name_2435_, v_args_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
lean_dec_ref(v_a_2438_);
lean_dec(v_a_2437_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(lean_object* v_decl_2444_, lean_object* v_k_2445_, lean_object* v_name_2446_, lean_object* v_args_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_2444_, v_k_2445_, v_name_2446_, v_args_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
lean_dec(v_a_2448_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object* v_k_2455_, lean_object* v_fvarId_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_2455_, v_fvarId_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object* v_decl_2464_, lean_object* v_k_2465_, lean_object* v_name_2466_, lean_object* v_numParams_2467_, lean_object* v_args_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_2464_, v_k_2465_, v_name_2466_, v_numParams_2467_, v_args_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object* v_fvarId_2476_, lean_object* v_sz_2477_, lean_object* v_i_2478_, lean_object* v_bs_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
size_t v_sz_boxed_2486_; size_t v_i_boxed_2487_; lean_object* v_res_2488_; 
v_sz_boxed_2486_ = lean_unbox_usize(v_sz_2477_);
lean_dec(v_sz_2477_);
v_i_boxed_2487_ = lean_unbox_usize(v_i_2478_);
lean_dec(v_i_2478_);
v_res_2488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2476_, v_sz_boxed_2486_, v_i_boxed_2487_, v_bs_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object* v_k_2489_, lean_object* v_decl_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_2489_, v_decl_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object* v_discr_2498_, lean_object* v_alt_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_discr_2498_, v_alt_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object* v_decl_2507_, lean_object* v_k_2508_, lean_object* v_name_2509_, lean_object* v_numParams_2510_, lean_object* v_args_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_2507_, v_k_2508_, v_name_2509_, v_numParams_2510_, v_args_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_args_2511_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* v_decl_2519_, lean_object* v_k_2520_, lean_object* v_ctorInfo_2521_, lean_object* v_fields_2522_, lean_object* v_irArgs_2523_, lean_object* v_i_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2519_, v_k_2520_, v_ctorInfo_2521_, v_fields_2522_, v_irArgs_2523_, v_i_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_irArgs_2523_);
lean_dec_ref(v_fields_2522_);
lean_dec_ref(v_ctorInfo_2521_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(lean_object* v_discr_2532_, lean_object* v_k_2533_, lean_object* v_ctorInfo_2534_, lean_object* v_params_2535_, lean_object* v_fields_2536_, lean_object* v_i_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2532_, v_k_2533_, v_ctorInfo_2534_, v_params_2535_, v_fields_2536_, v_i_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_fields_2536_);
lean_dec_ref(v_params_2535_);
lean_dec_ref(v_ctorInfo_2534_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(lean_object* v_c_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_c_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec(v_a_2546_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(lean_object* v_decl_2553_, lean_object* v_k_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2553_, v_k_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(lean_object* v_00_u03b1_2562_, lean_object* v_msg_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_2563_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(lean_object* v_00_u03b1_2571_, lean_object* v_msg_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(v_00_u03b1_2571_, v_msg_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(size_t v_sz_2580_, size_t v_i_2581_, lean_object* v_bs_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2580_, v_i_2581_, v_bs_2582_, v___y_2583_, v___y_2585_, v___y_2586_, v___y_2587_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(lean_object* v_sz_2590_, lean_object* v_i_2591_, lean_object* v_bs_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
size_t v_sz_boxed_2599_; size_t v_i_boxed_2600_; lean_object* v_res_2601_; 
v_sz_boxed_2599_ = lean_unbox_usize(v_sz_2590_);
lean_dec(v_sz_2590_);
v_i_boxed_2600_ = lean_unbox_usize(v_i_2591_);
lean_dec(v_i_2591_);
v_res_2601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(v_sz_boxed_2599_, v_i_boxed_2600_, v_bs_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(lean_object* v_as_2602_, size_t v_i_2603_, size_t v_stop_2604_, lean_object* v_b_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_2602_, v_i_2603_, v_stop_2604_, v_b_2605_, v___y_2606_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(lean_object* v_as_2613_, lean_object* v_i_2614_, lean_object* v_stop_2615_, lean_object* v_b_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
size_t v_i_boxed_2623_; size_t v_stop_boxed_2624_; lean_object* v_res_2625_; 
v_i_boxed_2623_ = lean_unbox_usize(v_i_2614_);
lean_dec(v_i_2614_);
v_stop_boxed_2624_ = lean_unbox_usize(v_stop_2615_);
lean_dec(v_stop_2615_);
v_res_2625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(v_as_2613_, v_i_boxed_2623_, v_stop_boxed_2624_, v_b_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v_as_2613_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(lean_object* v_upperBound_2626_, lean_object* v_params_2627_, lean_object* v___x_2628_, lean_object* v_discr_2629_, lean_object* v_inst_2630_, lean_object* v_R_2631_, lean_object* v_a_2632_, lean_object* v_b_2633_, lean_object* v_c_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_2626_, v_params_2627_, v___x_2628_, v_discr_2629_, v_a_2632_, v_b_2633_, v___y_2635_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(lean_object* v_upperBound_2642_, lean_object* v_params_2643_, lean_object* v___x_2644_, lean_object* v_discr_2645_, lean_object* v_inst_2646_, lean_object* v_R_2647_, lean_object* v_a_2648_, lean_object* v_b_2649_, lean_object* v_c_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(v_upperBound_2642_, v_params_2643_, v___x_2644_, v_discr_2645_, v_inst_2646_, v_R_2647_, v_a_2648_, v_b_2649_, v_c_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec(v___x_2644_);
lean_dec_ref(v_params_2643_);
lean_dec(v_upperBound_2642_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(size_t v_sz_2658_, size_t v_i_2659_, lean_object* v_bs_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_2658_, v_i_2659_, v_bs_2660_, v___y_2661_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___boxed(lean_object* v_sz_2668_, lean_object* v_i_2669_, lean_object* v_bs_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
size_t v_sz_boxed_2677_; size_t v_i_boxed_2678_; lean_object* v_res_2679_; 
v_sz_boxed_2677_ = lean_unbox_usize(v_sz_2668_);
lean_dec(v_sz_2668_);
v_i_boxed_2678_ = lean_unbox_usize(v_i_2669_);
lean_dec(v_i_2669_);
v_res_2679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(v_sz_boxed_2677_, v_i_boxed_2678_, v_bs_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(lean_object* v_upperBound_2680_, lean_object* v_fieldInfo_2681_, lean_object* v___x_2682_, lean_object* v_inst_2683_, lean_object* v_R_2684_, lean_object* v_a_2685_, lean_object* v_b_2686_, lean_object* v_c_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_2680_, v_fieldInfo_2681_, v___x_2682_, v_a_2685_, v_b_2686_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(lean_object* v_upperBound_2695_, lean_object* v_fieldInfo_2696_, lean_object* v___x_2697_, lean_object* v_inst_2698_, lean_object* v_R_2699_, lean_object* v_a_2700_, lean_object* v_b_2701_, lean_object* v_c_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(v_upperBound_2695_, v_fieldInfo_2696_, v___x_2697_, v_inst_2698_, v_R_2699_, v_a_2700_, v_b_2701_, v_c_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___x_2697_);
lean_dec_ref(v_fieldInfo_2696_);
lean_dec(v_upperBound_2695_);
return v_res_2709_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0));
v___x_2712_ = l_Lean_stringToMessageData(v___x_2711_);
return v___x_2712_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2));
v___x_2715_ = l_Lean_stringToMessageData(v___x_2714_);
return v___x_2715_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4));
v___x_2718_ = l_Lean_stringToMessageData(v___x_2717_);
return v___x_2718_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6));
v___x_2721_ = l_Lean_stringToMessageData(v___x_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(lean_object* v_decl_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_){
_start:
{
lean_object* v_toSignature_2729_; lean_object* v_value_2730_; uint8_t v_recursive_2731_; lean_object* v_inlineAttr_x3f_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2864_; 
v_toSignature_2729_ = lean_ctor_get(v_decl_2722_, 0);
v_value_2730_ = lean_ctor_get(v_decl_2722_, 1);
v_recursive_2731_ = lean_ctor_get_uint8(v_decl_2722_, sizeof(void*)*3);
v_inlineAttr_x3f_2732_ = lean_ctor_get(v_decl_2722_, 2);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_decl_2722_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2734_ = v_decl_2722_;
v_isShared_2735_ = v_isSharedCheck_2864_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_inlineAttr_x3f_2732_);
lean_inc(v_value_2730_);
lean_inc(v_toSignature_2729_);
lean_dec(v_decl_2722_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2864_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v_name_2736_; lean_object* v_levelParams_2737_; lean_object* v_type_2738_; lean_object* v_params_2739_; uint8_t v_safe_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2863_; 
v_name_2736_ = lean_ctor_get(v_toSignature_2729_, 0);
v_levelParams_2737_ = lean_ctor_get(v_toSignature_2729_, 1);
v_type_2738_ = lean_ctor_get(v_toSignature_2729_, 2);
v_params_2739_ = lean_ctor_get(v_toSignature_2729_, 3);
v_safe_2740_ = lean_ctor_get_uint8(v_toSignature_2729_, sizeof(void*)*4);
v_isSharedCheck_2863_ = !lean_is_exclusive(v_toSignature_2729_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2742_ = v_toSignature_2729_;
v_isShared_2743_ = v_isSharedCheck_2863_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_params_2739_);
lean_inc(v_type_2738_);
lean_inc(v_levelParams_2737_);
lean_inc(v_name_2736_);
lean_dec(v_toSignature_2729_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2863_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
size_t v_sz_2744_; size_t v___x_2745_; lean_object* v___x_2746_; 
v_sz_2744_ = lean_array_size(v_params_2739_);
v___x_2745_ = ((size_t)0ULL);
lean_inc_ref(v_params_2739_);
v___x_2746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2744_, v___x_2745_, v_params_2739_, v_a_2723_, v_a_2725_, v_a_2726_, v_a_2727_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref_known(v___x_2746_, 1);
v___x_2748_ = lean_array_get_size(v_params_2739_);
lean_dec_ref(v_params_2739_);
v___x_2749_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2738_, v___x_2748_, v_a_2726_, v_a_2727_);
lean_dec_ref(v_type_2738_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2846_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2752_ = v___x_2749_;
v_isShared_2753_ = v_isSharedCheck_2846_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2749_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2846_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; lean_object* v_env_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v___x_2754_ = lean_st_ref_get(v_a_2727_);
v_env_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc_ref(v_env_2755_);
lean_dec(v___x_2754_);
v___x_2756_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
lean_inc(v_name_2736_);
v___x_2757_ = l_Lean_TagAttribute_hasTag(v___x_2756_, v_env_2755_, v_name_2736_);
if (lean_obj_tag(v_value_2730_) == 0)
{
lean_object* v_code_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2808_; 
lean_del_object(v___x_2752_);
v_code_2758_ = lean_ctor_get(v_value_2730_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_value_2730_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2760_ = v_value_2730_;
v_isShared_2761_ = v_isSharedCheck_2808_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_code_2758_);
lean_dec(v_value_2730_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2808_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; 
if (v___x_2757_ == 0)
{
v___y_2763_ = v_a_2723_;
v___y_2764_ = v_a_2724_;
v___y_2765_ = v_a_2725_;
v___y_2766_ = v_a_2726_;
v___y_2767_ = v_a_2727_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_del_object(v___x_2760_);
lean_dec_ref(v_code_2758_);
lean_dec(v_a_2750_);
lean_dec(v_a_2747_);
lean_del_object(v___x_2742_);
lean_dec(v_levelParams_2737_);
lean_del_object(v___x_2734_);
lean_dec(v_inlineAttr_x3f_2732_);
v___x_2794_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1);
v___x_2795_ = l_Lean_MessageData_ofName(v_name_2736_);
v___x_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2794_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3);
v___x_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2796_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2798_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2799_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
v___jp_2762_:
{
lean_object* v___x_2768_; 
v___x_2768_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_2758_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2785_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2785_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2785_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 3, v_a_2747_);
lean_ctor_set(v___x_2742_, 2, v_a_2750_);
v___x_2774_ = v___x_2742_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_name_2736_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v_levelParams_2737_);
lean_ctor_set(v_reuseFailAlloc_2784_, 2, v_a_2750_);
lean_ctor_set(v_reuseFailAlloc_2784_, 3, v_a_2747_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, sizeof(void*)*4, v_safe_2740_);
v___x_2774_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2776_; 
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v_a_2769_);
v___x_2776_ = v___x_2760_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2769_);
v___x_2776_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2778_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___x_2776_);
lean_ctor_set(v___x_2734_, 0, v___x_2774_);
v___x_2778_ = v___x_2734_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2782_, 2, v_inlineAttr_x3f_2732_);
lean_ctor_set_uint8(v_reuseFailAlloc_2782_, sizeof(void*)*3, v_recursive_2731_);
v___x_2778_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2780_; 
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2778_);
v___x_2780_ = v___x_2771_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_del_object(v___x_2760_);
lean_dec(v_a_2750_);
lean_dec(v_a_2747_);
lean_del_object(v___x_2742_);
lean_dec(v_levelParams_2737_);
lean_dec(v_name_2736_);
lean_del_object(v___x_2734_);
lean_dec(v_inlineAttr_x3f_2732_);
v_a_2786_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2768_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2768_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
}
else
{
lean_object* v_externAttrData_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2845_; 
v_externAttrData_2809_ = lean_ctor_get(v_value_2730_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_value_2730_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2811_ = v_value_2730_;
v_isShared_2812_ = v_isSharedCheck_2845_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_externAttrData_2809_);
lean_dec(v_value_2730_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2845_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v_resultType_2814_; 
if (v___x_2757_ == 0)
{
v_resultType_2814_ = v_a_2750_;
goto v___jp_2813_;
}
else
{
uint8_t v___x_2827_; 
v___x_2827_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_2750_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; 
lean_dec(v_a_2750_);
v___x_2828_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
v_resultType_2814_ = v___x_2828_;
goto v___jp_2813_;
}
else
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_del_object(v___x_2811_);
lean_dec(v_externAttrData_2809_);
lean_del_object(v___x_2752_);
lean_dec(v_a_2747_);
lean_del_object(v___x_2742_);
lean_dec(v_levelParams_2737_);
lean_del_object(v___x_2734_);
lean_dec(v_inlineAttr_x3f_2732_);
v___x_2829_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5);
v___x_2830_ = l_Lean_MessageData_ofName(v_name_2736_);
v___x_2831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2829_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7);
v___x_2833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2831_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = l_Lean_MessageData_ofExpr(v_a_2750_);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2835_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2836_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
v___jp_2813_:
{
lean_object* v___x_2816_; 
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 3, v_a_2747_);
lean_ctor_set(v___x_2742_, 2, v_resultType_2814_);
v___x_2816_ = v___x_2742_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_name_2736_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_levelParams_2737_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_resultType_2814_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_a_2747_);
lean_ctor_set_uint8(v_reuseFailAlloc_2826_, sizeof(void*)*4, v_safe_2740_);
v___x_2816_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
lean_object* v___x_2818_; 
if (v_isShared_2812_ == 0)
{
v___x_2818_ = v___x_2811_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_externAttrData_2809_);
v___x_2818_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2820_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___x_2818_);
lean_ctor_set(v___x_2734_, 0, v___x_2816_);
v___x_2820_ = v___x_2734_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2824_, 2, v_inlineAttr_x3f_2732_);
lean_ctor_set_uint8(v_reuseFailAlloc_2824_, sizeof(void*)*3, v_recursive_2731_);
v___x_2820_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2822_; 
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2820_);
v___x_2822_ = v___x_2752_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
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
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_a_2747_);
lean_del_object(v___x_2742_);
lean_dec(v_levelParams_2737_);
lean_dec(v_name_2736_);
lean_del_object(v___x_2734_);
lean_dec(v_inlineAttr_x3f_2732_);
lean_dec_ref(v_value_2730_);
v_a_2847_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2749_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2749_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_del_object(v___x_2742_);
lean_dec_ref(v_params_2739_);
lean_dec_ref(v_type_2738_);
lean_dec(v_levelParams_2737_);
lean_dec(v_name_2736_);
lean_del_object(v___x_2734_);
lean_dec(v_inlineAttr_x3f_2732_);
lean_dec_ref(v_value_2730_);
v_a_2855_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2746_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2746_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___boxed(lean_object* v_decl_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
lean_dec(v_a_2866_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(lean_object* v_decl_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2882_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc_n(v_a_2881_, 2);
lean_dec_ref_known(v___x_2880_, 1);
v___x_2882_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_2881_, v_a_2878_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2889_ == 0)
{
lean_object* v_unused_2890_; 
v_unused_2890_ = lean_ctor_get(v___x_2882_, 0);
lean_dec(v_unused_2890_);
v___x_2884_ = v___x_2882_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_dec(v___x_2882_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v_a_2881_);
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2881_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec(v_a_2881_);
v_a_2891_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2882_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2882_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
else
{
return v___x_2880_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go___boxed(lean_object* v_decl_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
return v_res_2906_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2907_ = lean_box(0);
v___x_2908_ = lean_unsigned_to_nat(16u);
v___x_2909_ = lean_mk_array(v___x_2908_, v___x_2907_);
return v___x_2909_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2910_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0);
v___x_2911_ = lean_unsigned_to_nat(0u);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
lean_ctor_set(v___x_2912_, 1, v___x_2910_);
return v___x_2912_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2(void){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1);
v___x_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(lean_object* v_decl_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2921_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2);
v___x_2922_ = lean_st_mk_ref(v___x_2921_);
v___x_2923_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_2915_, v___x_2922_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2932_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2926_ = v___x_2923_;
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2928_ = lean_st_ref_get(v___x_2922_);
lean_dec(v___x_2922_);
lean_dec(v___x_2928_);
if (v_isShared_2927_ == 0)
{
v___x_2930_ = v___x_2926_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2924_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
else
{
lean_dec(v___x_2922_);
return v___x_2923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___boxed(lean_object* v_decl_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_decl_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(size_t v_sz_2940_, size_t v_i_2941_, lean_object* v_bs_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
uint8_t v___x_2948_; 
v___x_2948_ = lean_usize_dec_lt(v_i_2941_, v_sz_2940_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_bs_2942_);
return v___x_2949_;
}
else
{
lean_object* v_v_2950_; lean_object* v___x_2951_; 
v_v_2950_ = lean_array_uget_borrowed(v_bs_2942_, v_i_2941_);
lean_inc(v_v_2950_);
v___x_2951_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_v_2950_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; lean_object* v_bs_x27_2954_; size_t v___x_2955_; size_t v___x_2956_; lean_object* v___x_2957_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = lean_unsigned_to_nat(0u);
v_bs_x27_2954_ = lean_array_uset(v_bs_2942_, v_i_2941_, v___x_2953_);
v___x_2955_ = ((size_t)1ULL);
v___x_2956_ = lean_usize_add(v_i_2941_, v___x_2955_);
v___x_2957_ = lean_array_uset(v_bs_x27_2954_, v_i_2941_, v_a_2952_);
v_i_2941_ = v___x_2956_;
v_bs_2942_ = v___x_2957_;
goto _start;
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec_ref(v_bs_2942_);
v_a_2959_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2951_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2951_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0___boxed(lean_object* v_sz_2967_, lean_object* v_i_2968_, lean_object* v_bs_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
size_t v_sz_boxed_2975_; size_t v_i_boxed_2976_; lean_object* v_res_2977_; 
v_sz_boxed_2975_ = lean_unbox_usize(v_sz_2967_);
lean_dec(v_sz_2967_);
v_i_boxed_2976_ = lean_unbox_usize(v_i_2968_);
lean_dec(v_i_2968_);
v_res_2977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_boxed_2975_, v_i_boxed_2976_, v_bs_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0(lean_object* v_x_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
size_t v_sz_2984_; size_t v___x_2985_; lean_object* v___x_2986_; 
v_sz_2984_ = lean_array_size(v_x_2978_);
v___x_2985_ = ((size_t)0ULL);
v___x_2986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_2984_, v___x_2985_, v_x_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0___boxed(lean_object* v_x_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_Compiler_LCNF_toImpure___lam__0(v_x_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3044_; uint8_t v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3044_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3045_ = 1;
v___x_3046_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3047_ = l_Lean_registerTraceClass(v___x_3044_, v___x_3045_, v___x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2____boxed(lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
return v_res_3049_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
