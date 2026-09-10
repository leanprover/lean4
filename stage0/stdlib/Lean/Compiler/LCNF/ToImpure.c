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
v___x_386_ = lean_st_ref_put(v___y_373_, v___x_385_);
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
v___x_405_ = lean_st_ref_put(v_a_355_, v___x_404_);
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
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_35569__overap_752_; lean_object* v___x_753_; 
v___x_749_ = l_StateRefT_x27_instMonad___redArg(v___x_748_);
v___x_750_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0);
v___x_751_ = l_instInhabitedOfMonad___redArg(v___x_749_, v___x_750_);
v___x_35569__overap_752_ = lean_panic_fn_borrowed(v___x_751_, v_msg_702_);
lean_dec(v___x_751_);
lean_inc(v___y_707_);
lean_inc_ref(v___y_706_);
lean_inc(v___y_705_);
lean_inc_ref(v___y_704_);
lean_inc(v___y_703_);
v___x_753_ = lean_apply_6(v___x_35569__overap_752_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, lean_box(0));
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
v___x_785_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0);
v___x_786_ = lean_box(0);
v___x_787_ = lean_array_get_borrowed(v___x_785_, v_params_771_, v_a_774_);
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
v___x_800_ = lean_st_ref_put(v___y_776_, v___x_799_);
v_a_779_ = v___x_786_;
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
v___x_814_ = lean_st_ref_put(v___y_776_, v___x_813_);
v_a_779_ = v___x_786_;
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
lean_object* v_v_830_; lean_object* v_type_831_; lean_object* v___x_832_; lean_object* v_bs_x27_833_; uint8_t v___y_835_; uint8_t v___y_842_; uint8_t v___x_844_; 
v_v_830_ = lean_array_uget_borrowed(v_bs_828_, v_i_827_);
v_type_831_ = lean_ctor_get(v_v_830_, 2);
lean_inc_ref(v_type_831_);
v___x_832_ = lean_unsigned_to_nat(0u);
v_bs_x27_833_ = lean_array_uset(v_bs_828_, v_i_827_, v___x_832_);
v___x_844_ = l_Lean_Expr_isVoid(v_type_831_);
if (v___x_844_ == 0)
{
uint8_t v___x_845_; 
v___x_845_ = l_Lean_Expr_isErased(v_type_831_);
lean_dec_ref(v_type_831_);
v___y_842_ = v___x_845_;
goto v___jp_841_;
}
else
{
lean_dec_ref(v_type_831_);
v___y_842_ = v___x_844_;
goto v___jp_841_;
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
v___jp_841_:
{
if (v___y_842_ == 0)
{
v___y_835_ = v___x_829_;
goto v___jp_834_;
}
else
{
uint8_t v___x_843_; 
v___x_843_ = 0;
v___y_835_ = v___x_843_;
goto v___jp_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object* v_sz_846_, lean_object* v_i_847_, lean_object* v_bs_848_){
_start:
{
size_t v_sz_boxed_849_; size_t v_i_boxed_850_; lean_object* v_res_851_; 
v_sz_boxed_849_ = lean_unbox_usize(v_sz_846_);
lean_dec(v_sz_846_);
v_i_boxed_850_ = lean_unbox_usize(v_i_847_);
lean_dec(v_i_847_);
v_res_851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_boxed_849_, v_i_boxed_850_, v_bs_848_);
return v_res_851_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_852_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
lean_ctor_set(v___x_857_, 2, v___x_856_);
lean_ctor_set(v___x_857_, 3, v___x_856_);
lean_ctor_set(v___x_857_, 4, v___x_855_);
lean_ctor_set(v___x_857_, 5, v___x_855_);
lean_ctor_set(v___x_857_, 6, v___x_855_);
lean_ctor_set(v___x_857_, 7, v___x_855_);
lean_ctor_set(v___x_857_, 8, v___x_855_);
lean_ctor_set(v___x_857_, 9, v___x_855_);
lean_ctor_set(v___x_857_, 10, v___x_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(lean_object* v_msg_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_toCold_864_; lean_object* v_ref_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_toCold_864_ = lean_ctor_get(v___y_861_, 0);
v_ref_865_ = lean_ctor_get(v___y_861_, 2);
v___x_866_ = lean_st_ref_get(v___y_862_);
v___x_867_ = lean_st_ref_get(v___y_860_);
v___x_868_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_859_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_892_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_892_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_892_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_892_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_env_873_; lean_object* v_lctx_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_890_; 
v_env_873_ = lean_ctor_get(v___x_866_, 0);
lean_inc_ref(v_env_873_);
lean_dec(v___x_866_);
v_lctx_874_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v___x_867_, 1);
lean_dec(v_unused_891_);
v___x_876_ = v___x_867_;
v_isShared_877_ = v_isSharedCheck_890_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_lctx_874_);
lean_dec(v___x_867_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_890_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v_options_878_; uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v_options_878_ = lean_ctor_get(v_toCold_864_, 2);
v___x_879_ = lean_unbox(v_a_869_);
lean_dec(v_a_869_);
v___x_880_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_874_, v___x_879_);
lean_dec_ref(v_lctx_874_);
v___x_881_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2);
lean_inc_ref(v_options_878_);
v___x_882_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_882_, 0, v_env_873_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
lean_ctor_set(v___x_882_, 2, v___x_880_);
lean_ctor_set(v___x_882_, 3, v_options_878_);
if (v_isShared_877_ == 0)
{
lean_ctor_set_tag(v___x_876_, 3);
lean_ctor_set(v___x_876_, 1, v_msg_858_);
lean_ctor_set(v___x_876_, 0, v___x_882_);
v___x_884_ = v___x_876_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_msg_858_);
v___x_884_ = v_reuseFailAlloc_889_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
lean_inc(v_ref_865_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v_ref_865_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
if (v_isShared_872_ == 0)
{
lean_ctor_set_tag(v___x_871_, 1);
lean_ctor_set(v___x_871_, 0, v___x_885_);
v___x_887_ = v___x_871_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec(v___x_867_);
lean_dec(v___x_866_);
lean_dec_ref(v_msg_858_);
v_a_893_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_868_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_868_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(lean_object* v_msg_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(size_t v_sz_908_, size_t v_i_909_, lean_object* v_bs_910_, lean_object* v___y_911_){
_start:
{
uint8_t v___x_913_; 
v___x_913_ = lean_usize_dec_lt(v_i_909_, v_sz_908_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v_bs_910_);
return v___x_914_;
}
else
{
lean_object* v_v_915_; lean_object* v___x_916_; 
v_v_915_ = lean_array_uget_borrowed(v_bs_910_, v_i_909_);
lean_inc(v_v_915_);
v___x_916_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_v_915_, v___y_911_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; lean_object* v_bs_x27_919_; size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = lean_unsigned_to_nat(0u);
v_bs_x27_919_ = lean_array_uset(v_bs_910_, v_i_909_, v___x_918_);
v___x_920_ = ((size_t)1ULL);
v___x_921_ = lean_usize_add(v_i_909_, v___x_920_);
v___x_922_ = lean_array_uset(v_bs_x27_919_, v_i_909_, v_a_917_);
v_i_909_ = v___x_921_;
v_bs_910_ = v___x_922_;
goto _start;
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v_bs_910_);
v_a_924_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_916_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_916_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg___boxed(lean_object* v_sz_932_, lean_object* v_i_933_, lean_object* v_bs_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
size_t v_sz_boxed_937_; size_t v_i_boxed_938_; lean_object* v_res_939_; 
v_sz_boxed_937_ = lean_unbox_usize(v_sz_932_);
lean_dec(v_sz_932_);
v_i_boxed_938_ = lean_unbox_usize(v_i_933_);
lean_dec(v_i_933_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_boxed_937_, v_i_boxed_938_, v_bs_934_, v___y_935_);
lean_dec(v___y_935_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(lean_object* v_upperBound_940_, lean_object* v_fieldInfo_941_, lean_object* v___x_942_, lean_object* v_a_943_, lean_object* v_b_944_){
_start:
{
lean_object* v_a_947_; uint8_t v___x_951_; 
v___x_951_ = lean_nat_dec_lt(v_a_943_, v_upperBound_940_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
lean_dec(v_a_943_);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v_b_944_);
return v___x_952_;
}
else
{
lean_object* v___x_953_; 
v___x_953_ = lean_array_fget_borrowed(v_fieldInfo_941_, v_a_943_);
switch(lean_obj_tag(v___x_953_))
{
case 1:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = lean_box(0);
v___x_955_ = lean_array_get_borrowed(v___x_954_, v___x_942_, v_a_943_);
lean_inc(v___x_955_);
v___x_956_ = lean_array_push(v_b_944_, v___x_955_);
v_a_947_ = v___x_956_;
goto v___jp_946_;
}
case 2:
{
v_a_947_ = v_b_944_;
goto v___jp_946_;
}
case 3:
{
v_a_947_ = v_b_944_;
goto v___jp_946_;
}
default: 
{
v_a_947_ = v_b_944_;
goto v___jp_946_;
}
}
}
v___jp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = lean_nat_add(v_a_943_, v___x_948_);
lean_dec(v_a_943_);
v_a_943_ = v___x_949_;
v_b_944_ = v_a_947_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(lean_object* v_upperBound_957_, lean_object* v_fieldInfo_958_, lean_object* v___x_959_, lean_object* v_a_960_, lean_object* v_b_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_957_, v_fieldInfo_958_, v___x_959_, v_a_960_, v_b_961_);
lean_dec_ref(v___x_959_);
lean_dec_ref(v_fieldInfo_958_);
lean_dec(v_upperBound_957_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object* v_as_964_, size_t v_i_965_, size_t v_stop_966_, lean_object* v_b_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_a_971_; uint8_t v___x_975_; 
v___x_975_ = lean_usize_dec_eq(v_i_965_, v_stop_966_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v_snd_977_; uint8_t v___x_978_; 
v___x_976_ = lean_array_uget_borrowed(v_as_964_, v_i_965_);
v_snd_977_ = lean_ctor_get(v___x_976_, 1);
v___x_978_ = lean_unbox(v_snd_977_);
if (v___x_978_ == 0)
{
v_a_971_ = v_b_967_;
goto v___jp_970_;
}
else
{
lean_object* v_fst_979_; lean_object* v___x_980_; 
v_fst_979_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_fst_979_);
v___x_980_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_fst_979_, v___y_968_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = lean_array_push(v_b_967_, v_a_981_);
v_a_971_ = v___x_982_;
goto v___jp_970_;
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec_ref(v_b_967_);
v_a_983_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_980_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_980_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
else
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v_b_967_);
return v___x_991_;
}
v___jp_970_:
{
size_t v___x_972_; size_t v___x_973_; 
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_add(v_i_965_, v___x_972_);
v_i_965_ = v___x_973_;
v_b_967_ = v_a_971_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object* v_as_992_, lean_object* v_i_993_, lean_object* v_stop_994_, lean_object* v_b_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
size_t v_i_boxed_998_; size_t v_stop_boxed_999_; lean_object* v_res_1000_; 
v_i_boxed_998_ = lean_unbox_usize(v_i_993_);
lean_dec(v_i_993_);
v_stop_boxed_999_ = lean_unbox_usize(v_stop_994_);
lean_dec(v_stop_994_);
v_res_1000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_992_, v_i_boxed_998_, v_stop_boxed_999_, v_b_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v_as_992_);
return v_res_1000_;
}
}
static lean_object* _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0(void){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Array_instInhabited(lean_box(0));
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(lean_object* v_msg_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_obj_once(&l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0, &l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0_once, _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0);
v___x_1004_ = lean_panic_fn_borrowed(v___x_1003_, v_msg_1002_);
return v___x_1004_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1008_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2));
v___x_1009_ = lean_unsigned_to_nat(11u);
v___x_1010_ = lean_unsigned_to_nat(163u);
v___x_1011_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1));
v___x_1012_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0));
v___x_1013_ = l_mkPanicMessageWithDecl(v___x_1012_, v___x_1011_, v___x_1010_, v___x_1009_, v___x_1008_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(lean_object* v_a_1014_, lean_object* v_x_1015_){
_start:
{
if (lean_obj_tag(v_x_1015_) == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3);
v___x_1017_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(v___x_1016_);
return v___x_1017_;
}
else
{
lean_object* v_key_1018_; lean_object* v_value_1019_; lean_object* v_tail_1020_; uint8_t v___x_1021_; 
v_key_1018_ = lean_ctor_get(v_x_1015_, 0);
v_value_1019_ = lean_ctor_get(v_x_1015_, 1);
v_tail_1020_ = lean_ctor_get(v_x_1015_, 2);
v___x_1021_ = l_Lean_instBEqFVarId_beq(v_key_1018_, v_a_1014_);
if (v___x_1021_ == 0)
{
v_x_1015_ = v_tail_1020_;
goto _start;
}
else
{
lean_inc(v_value_1019_);
return v_value_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___boxed(lean_object* v_a_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_a_1023_, v_x_1024_);
lean_dec(v_x_1024_);
lean_dec(v_a_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(lean_object* v_m_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_buckets_1028_; lean_object* v___x_1029_; uint64_t v___x_1030_; uint64_t v___x_1031_; uint64_t v___x_1032_; uint64_t v_fold_1033_; uint64_t v___x_1034_; uint64_t v___x_1035_; uint64_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v_buckets_1028_ = lean_ctor_get(v_m_1026_, 1);
v___x_1029_ = lean_array_get_size(v_buckets_1028_);
v___x_1030_ = l_Lean_instHashableFVarId_hash(v_a_1027_);
v___x_1031_ = 32ULL;
v___x_1032_ = lean_uint64_shift_right(v___x_1030_, v___x_1031_);
v_fold_1033_ = lean_uint64_xor(v___x_1030_, v___x_1032_);
v___x_1034_ = 16ULL;
v___x_1035_ = lean_uint64_shift_right(v_fold_1033_, v___x_1034_);
v___x_1036_ = lean_uint64_xor(v_fold_1033_, v___x_1035_);
v___x_1037_ = lean_uint64_to_usize(v___x_1036_);
v___x_1038_ = lean_usize_of_nat(v___x_1029_);
v___x_1039_ = ((size_t)1ULL);
v___x_1040_ = lean_usize_sub(v___x_1038_, v___x_1039_);
v___x_1041_ = lean_usize_land(v___x_1037_, v___x_1040_);
v___x_1042_ = lean_array_uget_borrowed(v_buckets_1028_, v___x_1041_);
v___x_1043_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_a_1027_, v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(lean_object* v_m_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_m_1044_, v_a_1045_);
lean_dec(v_a_1045_);
lean_dec_ref(v_m_1044_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(size_t v_sz_1047_, size_t v_i_1048_, lean_object* v_bs_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
uint8_t v___x_1055_; 
v___x_1055_ = lean_usize_dec_lt(v_i_1048_, v_sz_1047_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1056_, 0, v_bs_1049_);
return v___x_1056_;
}
else
{
lean_object* v_v_1057_; lean_object* v___x_1058_; 
v_v_1057_ = lean_array_uget_borrowed(v_bs_1049_, v_i_1048_);
lean_inc(v_v_1057_);
v___x_1058_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_v_1057_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1060_; lean_object* v_bs_x27_1061_; size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = lean_unsigned_to_nat(0u);
v_bs_x27_1061_ = lean_array_uset(v_bs_1049_, v_i_1048_, v___x_1060_);
v___x_1062_ = ((size_t)1ULL);
v___x_1063_ = lean_usize_add(v_i_1048_, v___x_1062_);
v___x_1064_ = lean_array_uset(v_bs_x27_1061_, v_i_1048_, v_a_1059_);
v_i_1048_ = v___x_1063_;
v_bs_1049_ = v___x_1064_;
goto _start;
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec_ref(v_bs_1049_);
v_a_1066_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1058_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1058_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(lean_object* v_sz_1074_, lean_object* v_i_1075_, lean_object* v_bs_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
size_t v_sz_boxed_1082_; size_t v_i_boxed_1083_; lean_object* v_res_1084_; 
v_sz_boxed_1082_ = lean_unbox_usize(v_sz_1074_);
lean_dec(v_sz_1074_);
v_i_boxed_1083_ = lean_unbox_usize(v_i_1075_);
lean_dec(v_i_1075_);
v_res_1084_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_boxed_1082_, v_i_boxed_1083_, v_bs_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec(v___y_1077_);
return v_res_1084_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1087_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1));
v___x_1088_ = lean_unsigned_to_nat(12u);
v___x_1089_ = lean_unsigned_to_nat(116u);
v___x_1090_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1091_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1092_ = l_mkPanicMessageWithDecl(v___x_1091_, v___x_1090_, v___x_1089_, v___x_1088_, v___x_1087_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(lean_object* v_k_1093_, lean_object* v_decl_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___x_1101_; lean_object* v_lctx_1102_; lean_object* v_nextIdx_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1123_; 
v___x_1101_ = lean_st_ref_take(v_a_1097_);
v_lctx_1102_ = lean_ctor_get(v___x_1101_, 0);
v_nextIdx_1103_ = lean_ctor_get(v___x_1101_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1105_ = v___x_1101_;
v_isShared_1106_ = v_isSharedCheck_1123_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_nextIdx_1103_);
lean_inc(v_lctx_1102_);
lean_dec(v___x_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1123_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
uint8_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1107_ = 1;
lean_inc_ref(v_decl_1094_);
v___x_1108_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1107_, v_lctx_1102_, v_decl_1094_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1108_);
v___x_1110_ = v___x_1105_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_nextIdx_1103_);
v___x_1110_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_st_ref_put(v_a_1097_, v___x_1110_);
v___x_1112_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1093_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1121_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_decl_1094_);
lean_ctor_set(v___x_1117_, 1, v_a_1113_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1117_);
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
else
{
lean_dec_ref(v_decl_1094_);
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(lean_object* v_k_1124_, lean_object* v_fvarId_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___x_1132_; lean_object* v_subst_1133_; lean_object* v_jpParamMask_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1145_; 
v___x_1132_ = lean_st_ref_take(v_a_1126_);
v_subst_1133_ = lean_ctor_get(v___x_1132_, 0);
v_jpParamMask_1134_ = lean_ctor_get(v___x_1132_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1136_ = v___x_1132_;
v_isShared_1137_ = v_isSharedCheck_1145_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_jpParamMask_1134_);
lean_inc(v_subst_1133_);
lean_dec(v___x_1132_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1145_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1138_ = lean_box(0);
v___x_1139_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1133_, v_fvarId_1125_, v___x_1138_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1139_);
v___x_1141_ = v___x_1136_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_jpParamMask_1134_);
v___x_1141_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_st_ref_put(v_a_1126_, v___x_1141_);
v___x_1143_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1124_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
return v___x_1143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(lean_object* v_decl_1147_, lean_object* v_k_1148_, lean_object* v_name_1149_, lean_object* v_numParams_1150_, lean_object* v_args_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_fvarId_1158_; lean_object* v_binderName_1159_; lean_object* v_type_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1222_; 
v_fvarId_1158_ = lean_ctor_get(v_decl_1147_, 0);
v_binderName_1159_ = lean_ctor_get(v_decl_1147_, 1);
v_type_1160_ = lean_ctor_get(v_decl_1147_, 2);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_decl_1147_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v_decl_1147_, 3);
lean_dec(v_unused_1223_);
v___x_1162_ = v_decl_1147_;
v_isShared_1163_ = v_isSharedCheck_1222_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_type_1160_);
lean_inc(v_binderName_1159_);
lean_inc(v_fvarId_1158_);
lean_dec(v_decl_1147_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1222_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1160_, v_a_1155_, v_a_1156_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
v___x_1166_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1150_);
v___x_1167_ = l_Array_extract___redArg(v_args_1151_, v___x_1166_, v_numParams_1150_);
v___x_1168_ = 1;
v___x_1169_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0));
lean_inc(v_binderName_1159_);
v___x_1170_ = l_Lean_Name_str___override(v_binderName_1159_, v___x_1169_);
v___x_1171_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1172_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1172_, 0, v_name_1149_);
lean_ctor_set(v___x_1172_, 1, v___x_1167_);
v___x_1173_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1168_, v___x_1170_, v___x_1171_, v___x_1172_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v_fvarId_1175_; lean_object* v___x_1176_; lean_object* v_lctx_1177_; lean_object* v_nextIdx_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1205_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1173_, 1);
v_fvarId_1175_ = lean_ctor_get(v_a_1174_, 0);
v___x_1176_ = lean_st_ref_take(v_a_1154_);
v_lctx_1177_ = lean_ctor_get(v___x_1176_, 0);
v_nextIdx_1178_ = lean_ctor_get(v___x_1176_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1180_ = v___x_1176_;
v_isShared_1181_ = v_isSharedCheck_1205_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_nextIdx_1178_);
lean_inc(v_lctx_1177_);
lean_dec(v___x_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1205_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1182_ = lean_array_get_size(v_args_1151_);
v___x_1183_ = l_Array_extract___redArg(v_args_1151_, v_numParams_1150_, v___x_1182_);
lean_inc(v_fvarId_1175_);
v___x_1184_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1184_, 0, v_fvarId_1175_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1165_);
lean_dec(v_a_1165_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 3, v___x_1184_);
lean_ctor_set(v___x_1162_, 2, v___x_1185_);
v___x_1187_ = v___x_1162_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_fvarId_1158_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_binderName_1159_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v___x_1184_);
v___x_1187_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
lean_inc_ref(v___x_1187_);
v___x_1188_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1168_, v_lctx_1177_, v___x_1187_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1188_);
v___x_1190_ = v___x_1180_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_nextIdx_1178_);
v___x_1190_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_st_ref_put(v_a_1154_, v___x_1190_);
v___x_1192_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1148_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1202_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1187_);
lean_ctor_set(v___x_1197_, 1, v_a_1193_);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v_a_1174_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1198_);
v___x_1200_ = v___x_1195_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
else
{
lean_dec_ref(v___x_1187_);
lean_dec(v_a_1174_);
return v___x_1192_;
}
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v_a_1165_);
lean_del_object(v___x_1162_);
lean_dec(v_binderName_1159_);
lean_dec(v_fvarId_1158_);
lean_dec(v_numParams_1150_);
lean_dec_ref(v_k_1148_);
v_a_1206_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1173_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1173_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_del_object(v___x_1162_);
lean_dec(v_binderName_1159_);
lean_dec(v_fvarId_1158_);
lean_dec(v_numParams_1150_);
lean_dec(v_name_1149_);
lean_dec_ref(v_k_1148_);
v_a_1214_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1164_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1164_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(lean_object* v_decl_1224_, lean_object* v_k_1225_, lean_object* v_name_1226_, lean_object* v_args_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_fvarId_1234_; lean_object* v_binderName_1235_; lean_object* v_type_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1255_; 
v_fvarId_1234_ = lean_ctor_get(v_decl_1224_, 0);
v_binderName_1235_ = lean_ctor_get(v_decl_1224_, 1);
v_type_1236_ = lean_ctor_get(v_decl_1224_, 2);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_decl_1224_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v_decl_1224_, 3);
lean_dec(v_unused_1256_);
v___x_1238_ = v_decl_1224_;
v_isShared_1239_ = v_isSharedCheck_1255_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_type_1236_);
lean_inc(v_binderName_1235_);
lean_inc(v_fvarId_1234_);
lean_dec(v_decl_1224_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1255_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1236_, v_a_1231_, v_a_1232_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___x_1240_, 1);
v___x_1242_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1242_, 0, v_name_1226_);
lean_ctor_set(v___x_1242_, 1, v_args_1227_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 3, v___x_1242_);
lean_ctor_set(v___x_1238_, 2, v_a_1241_);
v___x_1244_ = v___x_1238_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_fvarId_1234_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_binderName_1235_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_a_1241_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; 
v___x_1245_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1225_, v___x_1244_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
return v___x_1245_;
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_del_object(v___x_1238_);
lean_dec(v_binderName_1235_);
lean_dec(v_fvarId_1234_);
lean_dec_ref(v_args_1227_);
lean_dec(v_name_1226_);
lean_dec_ref(v_k_1225_);
v_a_1247_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1240_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1240_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(lean_object* v_decl_1257_, lean_object* v_k_1258_, lean_object* v_name_1259_, lean_object* v_args_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_fvarId_1267_; lean_object* v_binderName_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1278_; 
v_fvarId_1267_ = lean_ctor_get(v_decl_1257_, 0);
v_binderName_1268_ = lean_ctor_get(v_decl_1257_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_decl_1257_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; lean_object* v_unused_1280_; 
v_unused_1279_ = lean_ctor_get(v_decl_1257_, 3);
lean_dec(v_unused_1279_);
v_unused_1280_ = lean_ctor_get(v_decl_1257_, 2);
lean_dec(v_unused_1280_);
v___x_1270_ = v_decl_1257_;
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_binderName_1268_);
lean_inc(v_fvarId_1267_);
lean_dec(v_decl_1257_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1272_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1273_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_1273_, 0, v_name_1259_);
lean_ctor_set(v___x_1273_, 1, v_args_1260_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 3, v___x_1273_);
lean_ctor_set(v___x_1270_, 2, v___x_1272_);
v___x_1275_ = v___x_1270_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_fvarId_1267_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_binderName_1268_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1276_; 
v___x_1276_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1258_, v___x_1275_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
return v___x_1276_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(lean_object* v_decl_1281_, lean_object* v_k_1282_, lean_object* v_name_1283_, lean_object* v_numParams_1284_, lean_object* v_args_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_numArgs_1292_; uint8_t v___x_1293_; 
v_numArgs_1292_ = lean_array_get_size(v_args_1285_);
v___x_1293_ = lean_nat_dec_lt(v_numArgs_1292_, v_numParams_1284_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; 
v___x_1294_ = lean_nat_dec_eq(v_numArgs_1292_, v_numParams_1284_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; 
v___x_1295_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_1281_, v_k_1282_, v_name_1283_, v_numParams_1284_, v_args_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec_ref(v_args_1285_);
return v___x_1295_;
}
else
{
lean_object* v___x_1296_; 
lean_dec(v_numParams_1284_);
v___x_1296_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1281_, v_k_1282_, v_name_1283_, v_args_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
return v___x_1296_;
}
}
else
{
lean_object* v___x_1297_; 
lean_dec(v_numParams_1284_);
v___x_1297_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_1281_, v_k_1282_, v_name_1283_, v_args_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
return v___x_1297_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1299_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3));
v___x_1300_ = lean_unsigned_to_nat(14u);
v___x_1301_ = lean_unsigned_to_nat(185u);
v___x_1302_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1303_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1304_ = l_mkPanicMessageWithDecl(v___x_1303_, v___x_1302_, v___x_1301_, v___x_1300_, v___x_1299_);
return v___x_1304_;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(lean_object* v_decl_1321_, lean_object* v_k_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___x_1337_; lean_object* v_fvarId_1338_; lean_object* v_binderName_1339_; lean_object* v_type_1340_; lean_object* v_value_1341_; lean_object* v_subst_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1794_; 
v___x_1337_ = lean_st_ref_get(v_a_1323_);
v_fvarId_1338_ = lean_ctor_get(v_decl_1321_, 0);
v_binderName_1339_ = lean_ctor_get(v_decl_1321_, 1);
v_type_1340_ = lean_ctor_get(v_decl_1321_, 2);
v_value_1341_ = lean_ctor_get(v_decl_1321_, 3);
v_subst_1342_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v___x_1337_, 1);
lean_dec(v_unused_1795_);
v___x_1344_ = v___x_1337_;
v_isShared_1345_ = v_isSharedCheck_1794_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_subst_1342_);
lean_dec(v___x_1337_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1794_;
goto v_resetjp_1343_;
}
v___jp_1329_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2);
v___x_1336_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1335_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
return v___x_1336_;
}
v_resetjp_1343_:
{
uint8_t v___x_1346_; uint8_t v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = 0;
v___x_1347_ = 1;
lean_inc(v_value_1341_);
v___x_1348_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v___x_1346_, v_subst_1342_, v_value_1341_, v___x_1347_);
lean_dec_ref(v_subst_1342_);
switch(lean_obj_tag(v___x_1348_))
{
case 0:
{
lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1365_; 
lean_inc(v_binderName_1339_);
lean_inc(v_fvarId_1338_);
lean_del_object(v___x_1344_);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_decl_1321_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; lean_object* v_unused_1367_; lean_object* v_unused_1368_; lean_object* v_unused_1369_; 
v_unused_1366_ = lean_ctor_get(v_decl_1321_, 3);
lean_dec(v_unused_1366_);
v_unused_1367_ = lean_ctor_get(v_decl_1321_, 2);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v_decl_1321_, 1);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v_decl_1321_, 0);
lean_dec(v_unused_1369_);
v___x_1350_ = v_decl_1321_;
v_isShared_1351_ = v_isSharedCheck_1365_;
goto v_resetjp_1349_;
}
else
{
lean_dec(v_decl_1321_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1365_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v_value_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1364_; 
v_value_1352_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1354_ = v___x_1348_;
v_isShared_1355_ = v_isSharedCheck_1364_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_value_1352_);
lean_dec(v___x_1348_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1364_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_value_1352_);
if (v_isShared_1355_ == 0)
{
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_value_1352_);
v___x_1358_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1360_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 3, v___x_1358_);
lean_ctor_set(v___x_1350_, 2, v___x_1356_);
v___x_1360_ = v___x_1350_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_fvarId_1338_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_binderName_1339_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1361_; 
v___x_1361_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1322_, v___x_1360_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1361_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1370_; 
lean_inc(v_fvarId_1338_);
lean_del_object(v___x_1344_);
lean_dec_ref(v_decl_1321_);
v___x_1370_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1322_, v_fvarId_1338_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1370_;
}
case 2:
{
lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1473_; 
lean_inc(v_binderName_1339_);
lean_inc(v_fvarId_1338_);
lean_del_object(v___x_1344_);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_decl_1321_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; 
v_unused_1474_ = lean_ctor_get(v_decl_1321_, 3);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v_decl_1321_, 2);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_decl_1321_, 1);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_decl_1321_, 0);
lean_dec(v_unused_1477_);
v___x_1372_ = v_decl_1321_;
v_isShared_1373_ = v_isSharedCheck_1473_;
goto v_resetjp_1371_;
}
else
{
lean_dec(v_decl_1321_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1473_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v_typeName_1374_; lean_object* v_idx_1375_; lean_object* v_struct_1376_; lean_object* v___x_1377_; 
v_typeName_1374_ = lean_ctor_get(v___x_1348_, 0);
lean_inc_n(v_typeName_1374_, 2);
v_idx_1375_ = lean_ctor_get(v___x_1348_, 1);
lean_inc(v_idx_1375_);
v_struct_1376_ = lean_ctor_get(v___x_1348_, 2);
lean_inc(v_struct_1376_);
lean_dec_ref_known(v___x_1348_, 3);
v___x_1377_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_1374_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
if (lean_obj_tag(v_a_1378_) == 1)
{
lean_object* v_val_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_typeName_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_binderName_1339_);
v_val_1379_ = lean_ctor_get(v_a_1378_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_a_1378_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1381_ = v_a_1378_;
v_isShared_1382_ = v_isSharedCheck_1415_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_val_1379_);
lean_dec(v_a_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1415_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v_fieldIdx_1383_; uint8_t v___x_1384_; 
v_fieldIdx_1383_ = lean_ctor_get(v_val_1379_, 2);
lean_inc(v_fieldIdx_1383_);
lean_dec(v_val_1379_);
v___x_1384_ = lean_nat_dec_eq(v_fieldIdx_1383_, v_idx_1375_);
lean_dec(v_idx_1375_);
lean_dec(v_fieldIdx_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v_subst_1386_; lean_object* v_jpParamMask_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1398_; 
lean_del_object(v___x_1381_);
lean_dec(v_struct_1376_);
v___x_1385_ = lean_st_ref_take(v_a_1323_);
v_subst_1386_ = lean_ctor_get(v___x_1385_, 0);
v_jpParamMask_1387_ = lean_ctor_get(v___x_1385_, 1);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1389_ = v___x_1385_;
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_jpParamMask_1387_);
lean_inc(v_subst_1386_);
lean_dec(v___x_1385_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1391_ = lean_box(0);
v___x_1392_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1386_, v_fvarId_1338_, v___x_1391_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1392_);
v___x_1394_ = v___x_1389_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_jpParamMask_1387_);
v___x_1394_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_st_ref_put(v_a_1323_, v___x_1394_);
v___x_1396_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1396_;
}
}
}
else
{
lean_object* v___x_1399_; lean_object* v_subst_1400_; lean_object* v_jpParamMask_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1414_; 
v___x_1399_ = lean_st_ref_take(v_a_1323_);
v_subst_1400_ = lean_ctor_get(v___x_1399_, 0);
v_jpParamMask_1401_ = lean_ctor_get(v___x_1399_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1403_ = v___x_1399_;
v_isShared_1404_ = v_isSharedCheck_1414_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_jpParamMask_1401_);
lean_inc(v_subst_1400_);
lean_dec(v___x_1399_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1414_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v_struct_1376_);
v___x_1406_ = v___x_1381_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_struct_1376_);
v___x_1406_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1407_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1400_, v_fvarId_1338_, v___x_1406_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1407_);
v___x_1409_ = v___x_1403_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_jpParamMask_1401_);
v___x_1409_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_st_ref_put(v_a_1323_, v___x_1409_);
v___x_1411_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1411_;
}
}
}
}
}
}
else
{
lean_object* v___x_1416_; lean_object* v_subst_1417_; lean_object* v___x_1418_; 
lean_dec(v_a_1378_);
v___x_1416_ = lean_st_ref_get(v_a_1323_);
v_subst_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc_ref(v_subst_1417_);
lean_dec(v___x_1416_);
v___x_1418_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1417_, v_struct_1376_, v___x_1347_);
lean_dec_ref(v_subst_1417_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_fvarId_1419_; lean_object* v___x_1420_; lean_object* v_env_1421_; uint8_t v___x_1422_; lean_object* v___x_1423_; 
v_fvarId_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_fvarId_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = lean_st_ref_get(v_a_1327_);
v_env_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc_ref(v_env_1421_);
lean_dec(v___x_1420_);
v___x_1422_ = 0;
v___x_1423_ = l_Lean_Environment_find_x3f(v_env_1421_, v_typeName_1374_, v___x_1422_);
if (lean_obj_tag(v___x_1423_) == 1)
{
lean_object* v_val_1424_; 
v_val_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_val_1424_);
lean_dec_ref_known(v___x_1423_, 1);
if (lean_obj_tag(v_val_1424_) == 5)
{
lean_object* v_val_1425_; lean_object* v_ctors_1426_; 
v_val_1425_ = lean_ctor_get(v_val_1424_, 0);
lean_inc_ref(v_val_1425_);
lean_dec_ref_known(v_val_1424_, 1);
v_ctors_1426_ = lean_ctor_get(v_val_1425_, 4);
lean_inc(v_ctors_1426_);
lean_dec_ref(v_val_1425_);
if (lean_obj_tag(v_ctors_1426_) == 1)
{
lean_object* v_tail_1427_; 
v_tail_1427_ = lean_ctor_get(v_ctors_1426_, 1);
if (lean_obj_tag(v_tail_1427_) == 0)
{
lean_object* v_head_1428_; lean_object* v___x_1429_; 
v_head_1428_ = lean_ctor_get(v_ctors_1426_, 0);
lean_inc(v_head_1428_);
lean_dec_ref_known(v_ctors_1426_, 2);
v___x_1429_ = l_Lean_Compiler_LCNF_getCtorLayout(v_head_1428_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v_ctorInfo_1431_; lean_object* v_fieldInfo_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v_fst_1436_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v_ctorInfo_1431_ = lean_ctor_get(v_a_1430_, 0);
lean_inc_ref(v_ctorInfo_1431_);
v_fieldInfo_1432_ = lean_ctor_get(v_a_1430_, 1);
lean_inc_ref(v_fieldInfo_1432_);
lean_dec(v_a_1430_);
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_array_get(v___x_1433_, v_fieldInfo_1432_, v_idx_1375_);
lean_dec(v_idx_1375_);
lean_dec_ref(v_fieldInfo_1432_);
v___x_1435_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_fvarId_1419_, v_ctorInfo_1431_, v___x_1434_);
lean_dec_ref(v_ctorInfo_1431_);
v_fst_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_fst_1436_);
if (lean_obj_tag(v_fst_1436_) == 1)
{
lean_object* v___x_1437_; 
lean_dec_ref(v___x_1435_);
lean_del_object(v___x_1372_);
lean_dec(v_binderName_1339_);
v___x_1437_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1322_, v_fvarId_1338_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1437_;
}
else
{
lean_object* v_snd_1438_; lean_object* v___x_1440_; 
v_snd_1438_ = lean_ctor_get(v___x_1435_, 1);
lean_inc(v_snd_1438_);
lean_dec_ref(v___x_1435_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 3, v_fst_1436_);
lean_ctor_set(v___x_1372_, 2, v_snd_1438_);
v___x_1440_ = v___x_1372_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_fvarId_1338_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_binderName_1339_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_snd_1438_);
lean_ctor_set(v_reuseFailAlloc_1442_, 3, v_fst_1436_);
v___x_1440_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; 
v___x_1441_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1322_, v___x_1440_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1441_;
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_fvarId_1419_);
lean_dec(v_idx_1375_);
lean_del_object(v___x_1372_);
lean_dec(v_binderName_1339_);
lean_dec(v_fvarId_1338_);
lean_dec_ref(v_k_1322_);
v_a_1443_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1429_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1429_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1426_, 2);
lean_dec(v_fvarId_1419_);
lean_dec(v_idx_1375_);
lean_del_object(v___x_1372_);
lean_dec(v_binderName_1339_);
lean_dec(v_fvarId_1338_);
lean_dec_ref(v_k_1322_);
v___y_1330_ = v_a_1323_;
v___y_1331_ = v_a_1324_;
v___y_1332_ = v_a_1325_;
v___y_1333_ = v_a_1326_;
v___y_1334_ = v_a_1327_;
goto v___jp_1329_;
}
}
else
{
lean_dec(v_ctors_1426_);
lean_dec(v_fvarId_1419_);
lean_dec(v_idx_1375_);
lean_del_object(v___x_1372_);
lean_dec(v_binderName_1339_);
lean_dec(v_fvarId_1338_);
lean_dec_ref(v_k_1322_);
v___y_1330_ = v_a_1323_;
v___y_1331_ = v_a_1324_;
v___y_1332_ = v_a_1325_;
v___y_1333_ = v_a_1326_;
v___y_1334_ = v_a_1327_;
goto v___jp_1329_;
}
}
else
{
lean_dec(v_val_1424_);
lean_dec(v_fvarId_1419_);
lean_dec(v_idx_1375_);
lean_del_object(v___x_1372_);
lean_dec(v_binderName_1339_);
lean_dec(v_fvarId_1338_);
lean_dec_ref(v_k_1322_);
v___y_1330_ = v_a_1323_;
v___y_1331_ = v_a_1324_;
v___y_1332_ = v_a_1325_;
v___y_1333_ = v_a_1326_;
v___y_1334_ = v_a_1327_;
goto v___jp_1329_;
}
}
else
{
lean_dec(v___x_1423_);
lean_dec(v_fvarId_1419_);
lean_dec(v_idx_1375_);
lean_del_object(v___x_1372_);
lean_dec(v_binderName_1339_);
lean_dec(v_fvarId_1338_);
lean_dec_ref(v_k_1322_);
v___y_1330_ = v_a_1323_;
v___y_1331_ = v_a_1324_;
v___y_1332_ = v_a_1325_;
v___y_1333_ = v_a_1326_;
v___y_1334_ = v_a_1327_;
goto v___jp_1329_;
}
}
else
{
lean_object* v___x_1451_; lean_object* v_subst_1452_; lean_object* v_jpParamMask_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1464_; 
lean_dec(v_idx_1375_);
lean_dec(v_typeName_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_binderName_1339_);
v___x_1451_ = lean_st_ref_take(v_a_1323_);
v_subst_1452_ = lean_ctor_get(v___x_1451_, 0);
v_jpParamMask_1453_ = lean_ctor_get(v___x_1451_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1455_ = v___x_1451_;
v_isShared_1456_ = v_isSharedCheck_1464_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_jpParamMask_1453_);
lean_inc(v_subst_1452_);
lean_dec(v___x_1451_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1464_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1457_ = lean_box(0);
v___x_1458_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1452_, v_fvarId_1338_, v___x_1457_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1458_);
v___x_1460_ = v___x_1455_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_jpParamMask_1453_);
v___x_1460_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_st_ref_put(v_a_1323_, v___x_1460_);
v___x_1462_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1462_;
}
}
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_struct_1376_);
lean_dec(v_idx_1375_);
lean_dec(v_typeName_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_binderName_1339_);
lean_dec(v_fvarId_1338_);
lean_dec_ref(v_k_1322_);
v_a_1465_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1377_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1377_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
case 3:
{
lean_object* v_declName_1478_; lean_object* v_args_1479_; size_t v_sz_1480_; size_t v___x_1481_; lean_object* v___x_1482_; 
v_declName_1478_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_declName_1478_);
v_args_1479_ = lean_ctor_get(v___x_1348_, 2);
lean_inc_ref_n(v_args_1479_, 2);
lean_dec_ref_known(v___x_1348_, 3);
v_sz_1480_ = lean_array_size(v_args_1479_);
v___x_1481_ = ((size_t)0ULL);
v___x_1482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_1480_, v___x_1481_, v_args_1479_, v_a_1323_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1484_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1482_, 1);
lean_inc(v_declName_1478_);
v___x_1484_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1478_, v_a_1327_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1484_, 1);
if (lean_obj_tag(v_a_1485_) == 1)
{
lean_object* v_val_1486_; lean_object* v_params_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref(v_args_1479_);
lean_del_object(v___x_1344_);
v_val_1486_ = lean_ctor_get(v_a_1485_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v_a_1485_, 1);
v_params_1487_ = lean_ctor_get(v_val_1486_, 3);
lean_inc_ref(v_params_1487_);
lean_dec(v_val_1486_);
v___x_1488_ = lean_array_get_size(v_params_1487_);
lean_dec_ref(v_params_1487_);
v___x_1489_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1321_, v_k_1322_, v_declName_1478_, v___x_1488_, v_a_1483_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1489_;
}
else
{
lean_object* v___x_1490_; 
lean_dec(v_a_1485_);
lean_inc(v_declName_1478_);
v___x_1490_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1478_, v_a_1327_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
if (lean_obj_tag(v_a_1491_) == 1)
{
lean_object* v_val_1492_; lean_object* v_toSignature_1493_; lean_object* v_params_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec_ref(v_args_1479_);
lean_del_object(v___x_1344_);
v_val_1492_ = lean_ctor_get(v_a_1491_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v_a_1491_, 1);
v_toSignature_1493_ = lean_ctor_get(v_val_1492_, 0);
lean_inc_ref(v_toSignature_1493_);
lean_dec(v_val_1492_);
v_params_1494_ = lean_ctor_get(v_toSignature_1493_, 3);
lean_inc_ref(v_params_1494_);
lean_dec_ref(v_toSignature_1493_);
v___x_1495_ = lean_array_get_size(v_params_1494_);
lean_dec_ref(v_params_1494_);
v___x_1496_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1321_, v_k_1322_, v_declName_1478_, v___x_1495_, v_a_1483_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1496_;
}
else
{
lean_object* v___x_1497_; lean_object* v_env_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; 
lean_dec(v_a_1491_);
v___x_1497_ = lean_st_ref_get(v_a_1327_);
v_env_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc_ref(v_env_1498_);
lean_dec(v___x_1497_);
v___x_1499_ = 0;
lean_inc(v_declName_1478_);
v___x_1500_ = l_Lean_Environment_find_x3f(v_env_1498_, v_declName_1478_, v___x_1499_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec(v_a_1483_);
lean_dec_ref(v_args_1479_);
lean_dec(v_declName_1478_);
lean_del_object(v___x_1344_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
v___x_1501_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4);
v___x_1502_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1501_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1502_;
}
else
{
lean_object* v_val_1503_; 
v_val_1503_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_val_1503_);
lean_dec_ref_known(v___x_1500_, 1);
switch(lean_obj_tag(v_val_1503_))
{
case 0:
{
lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1519_; 
lean_dec(v_a_1483_);
lean_dec_ref(v_args_1479_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_val_1503_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v_val_1503_, 0);
lean_dec(v_unused_1520_);
v___x_1505_ = v_val_1503_;
v_isShared_1506_ = v_isSharedCheck_1519_;
goto v_resetjp_1504_;
}
else
{
lean_dec(v_val_1503_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1519_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1508_ = l_Lean_Name_toString(v_declName_1478_, v___x_1347_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set_tag(v___x_1505_, 3);
lean_ctor_set(v___x_1505_, 0, v___x_1508_);
v___x_1510_ = v___x_1505_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 5);
lean_ctor_set(v___x_1344_, 1, v___x_1510_);
lean_ctor_set(v___x_1344_, 0, v___x_1507_);
v___x_1512_ = v___x_1344_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = l_Lean_MessageData_ofFormat(v___x_1514_);
v___x_1516_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1515_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1516_;
}
}
}
}
case 2:
{
lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1536_; 
lean_dec(v_a_1483_);
lean_dec_ref(v_args_1479_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_val_1503_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v_val_1503_, 0);
lean_dec(v_unused_1537_);
v___x_1522_ = v_val_1503_;
v_isShared_1523_ = v_isSharedCheck_1536_;
goto v_resetjp_1521_;
}
else
{
lean_dec(v_val_1503_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1536_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1524_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1525_ = l_Lean_Name_toString(v_declName_1478_, v___x_1347_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set_tag(v___x_1522_, 3);
lean_ctor_set(v___x_1522_, 0, v___x_1525_);
v___x_1527_ = v___x_1522_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1529_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 5);
lean_ctor_set(v___x_1344_, 1, v___x_1527_);
lean_ctor_set(v___x_1344_, 0, v___x_1524_);
v___x_1529_ = v___x_1344_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1530_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = l_Lean_MessageData_ofFormat(v___x_1531_);
v___x_1533_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1532_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1533_;
}
}
}
}
case 4:
{
lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_a_1483_);
lean_dec_ref(v_args_1479_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_val_1503_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; 
v_unused_1554_ = lean_ctor_get(v_val_1503_, 0);
lean_dec(v_unused_1554_);
v___x_1539_ = v_val_1503_;
v_isShared_1540_ = v_isSharedCheck_1553_;
goto v_resetjp_1538_;
}
else
{
lean_dec(v_val_1503_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1553_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1541_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1542_ = l_Lean_Name_toString(v_declName_1478_, v___x_1347_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 3);
lean_ctor_set(v___x_1539_, 0, v___x_1542_);
v___x_1544_ = v___x_1539_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 5);
lean_ctor_set(v___x_1344_, 1, v___x_1544_);
lean_ctor_set(v___x_1344_, 0, v___x_1541_);
v___x_1546_ = v___x_1344_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1547_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = l_Lean_MessageData_ofFormat(v___x_1548_);
v___x_1550_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1549_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1550_;
}
}
}
}
case 5:
{
lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_a_1483_);
lean_dec_ref(v_args_1479_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_val_1503_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v_val_1503_, 0);
lean_dec(v_unused_1571_);
v___x_1556_ = v_val_1503_;
v_isShared_1557_ = v_isSharedCheck_1570_;
goto v_resetjp_1555_;
}
else
{
lean_dec(v_val_1503_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1570_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1558_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1559_ = l_Lean_Name_toString(v_declName_1478_, v___x_1347_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set_tag(v___x_1556_, 3);
lean_ctor_set(v___x_1556_, 0, v___x_1559_);
v___x_1561_ = v___x_1556_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1563_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 5);
lean_ctor_set(v___x_1344_, 1, v___x_1561_);
lean_ctor_set(v___x_1344_, 0, v___x_1558_);
v___x_1563_ = v___x_1344_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1564_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Lean_MessageData_ofFormat(v___x_1565_);
v___x_1567_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1566_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1567_;
}
}
}
}
case 6:
{
lean_object* v_val_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1707_; 
v_val_1572_ = lean_ctor_get(v_val_1503_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_val_1503_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1574_ = v_val_1503_;
v_isShared_1575_ = v_isSharedCheck_1707_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_val_1572_);
lean_dec(v_val_1503_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1707_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v_induct_1576_; lean_object* v_cidx_1577_; lean_object* v_numParams_1578_; lean_object* v___x_1579_; 
v_induct_1576_ = lean_ctor_get(v_val_1572_, 1);
lean_inc_n(v_induct_1576_, 2);
v_cidx_1577_ = lean_ctor_get(v_val_1572_, 2);
lean_inc(v_cidx_1577_);
v_numParams_1578_ = lean_ctor_get(v_val_1572_, 3);
lean_inc(v_numParams_1578_);
lean_dec_ref(v_val_1572_);
v___x_1579_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_induct_1576_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
if (lean_obj_tag(v_a_1580_) == 1)
{
lean_object* v_val_1581_; lean_object* v___x_1582_; lean_object* v_numParams_1583_; lean_object* v_fieldIdx_1584_; lean_object* v_subst_1585_; lean_object* v_jpParamMask_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1599_; 
lean_inc(v_fvarId_1338_);
lean_dec(v_numParams_1578_);
lean_dec(v_cidx_1577_);
lean_dec(v_induct_1576_);
lean_del_object(v___x_1574_);
lean_dec(v_a_1483_);
lean_dec(v_declName_1478_);
lean_del_object(v___x_1344_);
lean_dec_ref(v_decl_1321_);
v_val_1581_ = lean_ctor_get(v_a_1580_, 0);
lean_inc(v_val_1581_);
lean_dec_ref_known(v_a_1580_, 1);
v___x_1582_ = lean_st_ref_take(v_a_1323_);
v_numParams_1583_ = lean_ctor_get(v_val_1581_, 1);
lean_inc(v_numParams_1583_);
v_fieldIdx_1584_ = lean_ctor_get(v_val_1581_, 2);
lean_inc(v_fieldIdx_1584_);
lean_dec(v_val_1581_);
v_subst_1585_ = lean_ctor_get(v___x_1582_, 0);
v_jpParamMask_1586_ = lean_ctor_get(v___x_1582_, 1);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1588_ = v___x_1582_;
v_isShared_1589_ = v_isSharedCheck_1599_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_jpParamMask_1586_);
lean_inc(v_subst_1585_);
lean_dec(v___x_1582_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1599_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1590_ = lean_box(0);
v___x_1591_ = lean_nat_add(v_numParams_1583_, v_fieldIdx_1584_);
lean_dec(v_fieldIdx_1584_);
lean_dec(v_numParams_1583_);
v___x_1592_ = lean_array_get(v___x_1590_, v_args_1479_, v___x_1591_);
lean_dec(v___x_1591_);
lean_dec_ref(v_args_1479_);
v___x_1593_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1585_, v_fvarId_1338_, v___x_1592_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1593_);
v___x_1595_ = v___x_1588_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_jpParamMask_1586_);
v___x_1595_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = lean_st_ref_put(v_a_1323_, v___x_1595_);
v___x_1597_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1597_;
}
}
}
else
{
lean_object* v___x_1600_; 
lean_dec(v_a_1580_);
lean_dec_ref(v_args_1479_);
v___x_1600_ = l_Lean_Compiler_LCNF_nameToImpureType(v_induct_1576_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; uint8_t v___x_1602_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1600_, 1);
v___x_1602_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; 
lean_dec(v_a_1601_);
lean_dec(v_cidx_1577_);
lean_del_object(v___x_1574_);
v___x_1603_ = l_Lean_Compiler_LCNF_getCtorLayout(v_declName_1478_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1666_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1666_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1666_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v_ctorInfo_1613_; lean_object* v_fieldInfo_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1665_; 
v_ctorInfo_1613_ = lean_ctor_get(v_a_1604_, 0);
v_fieldInfo_1614_ = lean_ctor_get(v_a_1604_, 1);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_a_1604_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1616_ = v_a_1604_;
v_isShared_1617_ = v_isSharedCheck_1665_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_fieldInfo_1614_);
lean_inc(v_ctorInfo_1613_);
lean_dec(v_a_1604_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1665_;
goto v_resetjp_1615_;
}
v___jp_1608_:
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1609_);
v___x_1611_ = v___x_1606_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1618_ = lean_array_get_size(v_a_1483_);
v___x_1619_ = l_Array_extract___redArg(v_a_1483_, v_numParams_1578_, v___x_1618_);
lean_dec(v_a_1483_);
v___x_1620_ = lean_array_get_size(v___x_1619_);
v___x_1621_ = lean_array_get_size(v_fieldInfo_1614_);
v___x_1622_ = lean_nat_dec_eq(v___x_1620_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_dec_ref(v___x_1619_);
lean_del_object(v___x_1616_);
lean_dec_ref(v_fieldInfo_1614_);
lean_dec_ref(v_ctorInfo_1613_);
lean_del_object(v___x_1344_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
goto v___jp_1608_;
}
else
{
if (v___x_1602_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_del_object(v___x_1606_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_1625_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1621_, v_fieldInfo_1614_, v___x_1619_, v___x_1623_, v___x_1624_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1627_; lean_object* v_lctx_1628_; lean_object* v_nextIdx_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1656_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1627_ = lean_st_ref_take(v_a_1325_);
v_lctx_1628_ = lean_ctor_get(v___x_1627_, 0);
v_nextIdx_1629_ = lean_ctor_get(v___x_1627_, 1);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1631_ = v___x_1627_;
v_isShared_1632_ = v_isSharedCheck_1656_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_nextIdx_1629_);
lean_inc(v_lctx_1628_);
lean_dec(v___x_1627_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1656_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1636_; 
v___x_1633_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_ctorInfo_1613_);
v___x_1634_ = 1;
lean_inc_ref(v_ctorInfo_1613_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set_tag(v___x_1616_, 5);
lean_ctor_set(v___x_1616_, 1, v_a_1626_);
v___x_1636_ = v___x_1616_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_ctorInfo_1613_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_a_1626_);
v___x_1636_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1640_; 
lean_inc(v_binderName_1339_);
lean_inc(v_fvarId_1338_);
v___x_1637_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1637_, 0, v_fvarId_1338_);
lean_ctor_set(v___x_1637_, 1, v_binderName_1339_);
lean_ctor_set(v___x_1637_, 2, v___x_1633_);
lean_ctor_set(v___x_1637_, 3, v___x_1636_);
lean_inc_ref(v___x_1637_);
v___x_1638_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1634_, v_lctx_1628_, v___x_1637_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1638_);
v___x_1640_ = v___x_1631_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_nextIdx_1629_);
v___x_1640_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = lean_st_ref_put(v_a_1325_, v___x_1640_);
v___x_1642_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_1321_, v_k_1322_, v_ctorInfo_1613_, v_fieldInfo_1614_, v___x_1619_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec_ref(v___x_1619_);
lean_dec_ref(v_fieldInfo_1614_);
lean_dec_ref(v_ctorInfo_1613_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1653_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1653_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1653_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v_a_1643_);
lean_ctor_set(v___x_1344_, 0, v___x_1637_);
v___x_1648_ = v___x_1344_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1650_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1648_);
v___x_1650_ = v___x_1645_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1637_, 4);
lean_del_object(v___x_1344_);
return v___x_1642_;
}
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec_ref(v___x_1619_);
lean_del_object(v___x_1616_);
lean_dec_ref(v_fieldInfo_1614_);
lean_dec_ref(v_ctorInfo_1613_);
lean_del_object(v___x_1344_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
v_a_1657_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1625_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1625_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_dec_ref(v___x_1619_);
lean_del_object(v___x_1616_);
lean_dec_ref(v_fieldInfo_1614_);
lean_dec_ref(v_ctorInfo_1613_);
lean_del_object(v___x_1344_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
goto v___jp_1608_;
}
}
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v_numParams_1578_);
lean_dec(v_a_1483_);
lean_del_object(v___x_1344_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
v_a_1667_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1603_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1603_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1686_; 
lean_inc(v_binderName_1339_);
lean_inc(v_fvarId_1338_);
lean_dec(v_numParams_1578_);
lean_dec(v_a_1483_);
lean_dec(v_declName_1478_);
lean_del_object(v___x_1344_);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_decl_1321_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; lean_object* v_unused_1688_; lean_object* v_unused_1689_; lean_object* v_unused_1690_; 
v_unused_1687_ = lean_ctor_get(v_decl_1321_, 3);
lean_dec(v_unused_1687_);
v_unused_1688_ = lean_ctor_get(v_decl_1321_, 2);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_decl_1321_, 1);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_decl_1321_, 0);
lean_dec(v_unused_1690_);
v___x_1676_ = v_decl_1321_;
v_isShared_1677_ = v_isSharedCheck_1686_;
goto v_resetjp_1675_;
}
else
{
lean_dec(v_decl_1321_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1686_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_1601_, v_cidx_1577_);
lean_dec(v_cidx_1577_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1678_);
v___x_1680_ = v___x_1574_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1682_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 3, v___x_1680_);
lean_ctor_set(v___x_1676_, 2, v_a_1601_);
v___x_1682_ = v___x_1676_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_fvarId_1338_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_binderName_1339_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_a_1601_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; 
v___x_1683_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1322_, v___x_1682_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1683_;
}
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_numParams_1578_);
lean_dec(v_cidx_1577_);
lean_del_object(v___x_1574_);
lean_dec(v_a_1483_);
lean_dec(v_declName_1478_);
lean_del_object(v___x_1344_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
v_a_1691_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1600_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1600_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_numParams_1578_);
lean_dec(v_cidx_1577_);
lean_dec(v_induct_1576_);
lean_del_object(v___x_1574_);
lean_dec(v_a_1483_);
lean_dec_ref(v_args_1479_);
lean_dec(v_declName_1478_);
lean_del_object(v___x_1344_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
v_a_1699_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1579_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1579_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
case 7:
{
lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_a_1483_);
lean_dec_ref(v_args_1479_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_val_1503_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; 
v_unused_1724_ = lean_ctor_get(v_val_1503_, 0);
lean_dec(v_unused_1724_);
v___x_1709_ = v_val_1503_;
v_isShared_1710_ = v_isSharedCheck_1723_;
goto v_resetjp_1708_;
}
else
{
lean_dec(v_val_1503_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1723_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1711_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11));
v___x_1712_ = l_Lean_Name_toString(v_declName_1478_, v___x_1347_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set_tag(v___x_1709_, 3);
lean_ctor_set(v___x_1709_, 0, v___x_1712_);
v___x_1714_ = v___x_1709_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 5);
lean_ctor_set(v___x_1344_, 1, v___x_1714_);
lean_ctor_set(v___x_1344_, 0, v___x_1711_);
v___x_1716_ = v___x_1344_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1717_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13));
v___x_1718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1716_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = l_Lean_MessageData_ofFormat(v___x_1718_);
v___x_1720_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1719_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1720_;
}
}
}
}
default: 
{
lean_object* v___x_1725_; 
lean_dec(v_val_1503_);
lean_dec_ref(v_args_1479_);
lean_del_object(v___x_1344_);
v___x_1725_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1321_, v_k_1322_, v_declName_1478_, v_a_1483_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1725_;
}
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_a_1483_);
lean_dec_ref(v_args_1479_);
lean_dec(v_declName_1478_);
lean_del_object(v___x_1344_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
v_a_1726_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1490_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1490_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v_a_1483_);
lean_dec_ref(v_args_1479_);
lean_dec(v_declName_1478_);
lean_del_object(v___x_1344_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
v_a_1734_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1484_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1484_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v_args_1479_);
lean_dec(v_declName_1478_);
lean_del_object(v___x_1344_);
lean_dec_ref(v_k_1322_);
lean_dec_ref(v_decl_1321_);
v_a_1742_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1482_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1482_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
default: 
{
lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1789_; 
lean_inc_ref(v_type_1340_);
lean_inc(v_binderName_1339_);
lean_inc(v_fvarId_1338_);
lean_del_object(v___x_1344_);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_decl_1321_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; lean_object* v_unused_1791_; lean_object* v_unused_1792_; lean_object* v_unused_1793_; 
v_unused_1790_ = lean_ctor_get(v_decl_1321_, 3);
lean_dec(v_unused_1790_);
v_unused_1791_ = lean_ctor_get(v_decl_1321_, 2);
lean_dec(v_unused_1791_);
v_unused_1792_ = lean_ctor_get(v_decl_1321_, 1);
lean_dec(v_unused_1792_);
v_unused_1793_ = lean_ctor_get(v_decl_1321_, 0);
lean_dec(v_unused_1793_);
v___x_1751_ = v_decl_1321_;
v_isShared_1752_ = v_isSharedCheck_1789_;
goto v_resetjp_1750_;
}
else
{
lean_dec(v_decl_1321_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1789_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_fvarId_1753_; lean_object* v_args_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1788_; 
v_fvarId_1753_ = lean_ctor_get(v___x_1348_, 0);
v_args_1754_ = lean_ctor_get(v___x_1348_, 1);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1756_ = v___x_1348_;
v_isShared_1757_ = v_isSharedCheck_1788_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_args_1754_);
lean_inc(v_fvarId_1753_);
lean_dec(v___x_1348_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1788_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
size_t v_sz_1758_; size_t v___x_1759_; lean_object* v___x_1760_; 
v_sz_1758_ = lean_array_size(v_args_1754_);
v___x_1759_ = ((size_t)0ULL);
v___x_1760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_1758_, v___x_1759_, v_args_1754_, v_a_1323_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1762_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v___x_1762_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1340_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1763_);
lean_dec(v_a_1763_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v_a_1761_);
v___x_1766_ = v___x_1756_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_fvarId_1753_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1768_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 3, v___x_1766_);
lean_ctor_set(v___x_1751_, 2, v___x_1764_);
v___x_1768_ = v___x_1751_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_fvarId_1338_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_binderName_1339_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1770_, 3, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1769_; 
v___x_1769_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1322_, v___x_1768_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1769_;
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec(v_a_1761_);
lean_del_object(v___x_1756_);
lean_dec(v_fvarId_1753_);
lean_del_object(v___x_1751_);
lean_dec(v_binderName_1339_);
lean_dec(v_fvarId_1338_);
lean_dec_ref(v_k_1322_);
v_a_1772_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1762_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1762_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_del_object(v___x_1756_);
lean_dec(v_fvarId_1753_);
lean_del_object(v___x_1751_);
lean_dec_ref(v_type_1340_);
lean_dec(v_binderName_1339_);
lean_dec(v_fvarId_1338_);
lean_dec_ref(v_k_1322_);
v_a_1780_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1760_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1760_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
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
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1798_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1));
v___x_1799_ = lean_unsigned_to_nat(15u);
v___x_1800_ = lean_unsigned_to_nat(272u);
v___x_1801_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1802_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1803_ = l_mkPanicMessageWithDecl(v___x_1802_, v___x_1801_, v___x_1800_, v___x_1799_, v___x_1798_);
return v___x_1803_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1807_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5));
v___x_1808_ = lean_unsigned_to_nat(6u);
v___x_1809_ = lean_unsigned_to_nat(251u);
v___x_1810_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1811_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1812_ = l_mkPanicMessageWithDecl(v___x_1811_, v___x_1810_, v___x_1809_, v___x_1808_, v___x_1807_);
return v___x_1812_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7(void){
_start:
{
uint8_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = 0;
v___x_1814_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1813_);
return v___x_1814_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1816_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8));
v___x_1817_ = lean_unsigned_to_nat(6u);
v___x_1818_ = lean_unsigned_to_nat(253u);
v___x_1819_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1820_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1821_ = l_mkPanicMessageWithDecl(v___x_1820_, v___x_1819_, v___x_1818_, v___x_1817_, v___x_1816_);
return v___x_1821_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1823_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10));
v___x_1824_ = lean_unsigned_to_nat(6u);
v___x_1825_ = lean_unsigned_to_nat(254u);
v___x_1826_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1827_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1828_ = l_mkPanicMessageWithDecl(v___x_1827_, v___x_1826_, v___x_1825_, v___x_1824_, v___x_1823_);
return v___x_1828_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1830_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12));
v___x_1831_ = lean_unsigned_to_nat(45u);
v___x_1832_ = lean_unsigned_to_nat(252u);
v___x_1833_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1834_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1835_ = l_mkPanicMessageWithDecl(v___x_1834_, v___x_1833_, v___x_1832_, v___x_1831_, v___x_1830_);
return v___x_1835_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1838_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1));
v___x_1839_ = lean_unsigned_to_nat(18u);
v___x_1840_ = lean_unsigned_to_nat(293u);
v___x_1841_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0));
v___x_1842_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1843_ = l_mkPanicMessageWithDecl(v___x_1842_, v___x_1841_, v___x_1840_, v___x_1839_, v___x_1838_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object* v_discr_1844_, lean_object* v_k_1845_, lean_object* v_ctorInfo_1846_, lean_object* v_params_1847_, lean_object* v_fields_1848_, lean_object* v_i_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1926_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1932_ = lean_array_get_size(v_params_1847_);
v___x_1933_ = lean_nat_dec_lt(v_i_1849_, v___x_1932_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_box(0);
v___y_1926_ = v___x_1934_;
goto v___jp_1925_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_array_fget_borrowed(v_params_1847_, v_i_1849_);
lean_inc(v___x_1935_);
v___x_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
v___y_1926_ = v___x_1936_;
goto v___jp_1925_;
}
v___jp_1856_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2);
v___x_1863_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1862_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
return v___x_1863_;
}
v___jp_1864_:
{
if (lean_obj_tag(v___y_1865_) == 0)
{
lean_dec(v_i_1849_);
lean_dec(v_discr_1844_);
if (lean_obj_tag(v___y_1866_) == 0)
{
lean_object* v___x_1867_; 
v___x_1867_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1845_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
return v___x_1867_;
}
else
{
lean_dec(v___y_1866_);
lean_dec_ref(v_k_1845_);
v___y_1857_ = v_a_1850_;
v___y_1858_ = v_a_1851_;
v___y_1859_ = v_a_1852_;
v___y_1860_ = v_a_1853_;
v___y_1861_ = v_a_1854_;
goto v___jp_1856_;
}
}
else
{
if (lean_obj_tag(v___y_1866_) == 1)
{
lean_object* v_val_1868_; lean_object* v_val_1869_; lean_object* v___x_1870_; lean_object* v_fst_1871_; 
v_val_1868_ = lean_ctor_get(v___y_1865_, 0);
lean_inc(v_val_1868_);
lean_dec_ref_known(v___y_1865_, 1);
v_val_1869_ = lean_ctor_get(v___y_1866_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v___y_1866_, 1);
lean_inc(v_discr_1844_);
v___x_1870_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_discr_1844_, v_ctorInfo_1846_, v_val_1869_);
v_fst_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_fst_1871_);
if (lean_obj_tag(v_fst_1871_) == 1)
{
lean_object* v___x_1872_; lean_object* v_fvarId_1873_; lean_object* v_subst_1874_; lean_object* v_jpParamMask_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref(v___x_1870_);
v___x_1872_ = lean_st_ref_take(v_a_1850_);
v_fvarId_1873_ = lean_ctor_get(v_val_1868_, 0);
lean_inc(v_fvarId_1873_);
lean_dec(v_val_1868_);
v_subst_1874_ = lean_ctor_get(v___x_1872_, 0);
v_jpParamMask_1875_ = lean_ctor_get(v___x_1872_, 1);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1877_ = v___x_1872_;
v_isShared_1878_ = v_isSharedCheck_1888_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_jpParamMask_1875_);
lean_inc(v_subst_1874_);
lean_dec(v___x_1872_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1888_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1879_ = lean_box(0);
v___x_1880_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1874_, v_fvarId_1873_, v___x_1879_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1880_);
v___x_1882_ = v___x_1877_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_jpParamMask_1875_);
v___x_1882_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = lean_st_ref_put(v_a_1850_, v___x_1882_);
v___x_1884_ = lean_unsigned_to_nat(1u);
v___x_1885_ = lean_nat_add(v_i_1849_, v___x_1884_);
lean_dec(v_i_1849_);
v_i_1849_ = v___x_1885_;
goto _start;
}
}
}
else
{
lean_object* v_snd_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1923_; 
v_snd_1889_ = lean_ctor_get(v___x_1870_, 1);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1923_ == 0)
{
lean_object* v_unused_1924_; 
v_unused_1924_ = lean_ctor_get(v___x_1870_, 0);
lean_dec(v_unused_1924_);
v___x_1891_ = v___x_1870_;
v_isShared_1892_ = v_isSharedCheck_1923_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snd_1889_);
lean_dec(v___x_1870_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1923_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v_fvarId_1894_; lean_object* v_binderName_1895_; lean_object* v_lctx_1896_; lean_object* v_nextIdx_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1922_; 
v___x_1893_ = lean_st_ref_take(v_a_1852_);
v_fvarId_1894_ = lean_ctor_get(v_val_1868_, 0);
lean_inc(v_fvarId_1894_);
v_binderName_1895_ = lean_ctor_get(v_val_1868_, 1);
lean_inc(v_binderName_1895_);
lean_dec(v_val_1868_);
v_lctx_1896_ = lean_ctor_get(v___x_1893_, 0);
v_nextIdx_1897_ = lean_ctor_get(v___x_1893_, 1);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1899_ = v___x_1893_;
v_isShared_1900_ = v_isSharedCheck_1922_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_nextIdx_1897_);
lean_inc(v_lctx_1896_);
lean_dec(v___x_1893_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1922_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
uint8_t v___x_1901_; lean_object* v_decl_1902_; lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1901_ = 1;
v_decl_1902_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_1902_, 0, v_fvarId_1894_);
lean_ctor_set(v_decl_1902_, 1, v_binderName_1895_);
lean_ctor_set(v_decl_1902_, 2, v_snd_1889_);
lean_ctor_set(v_decl_1902_, 3, v_fst_1871_);
lean_inc_ref(v_decl_1902_);
v___x_1903_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1901_, v_lctx_1896_, v_decl_1902_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1903_);
v___x_1905_ = v___x_1899_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_nextIdx_1897_);
v___x_1905_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1906_ = lean_st_ref_put(v_a_1852_, v___x_1905_);
v___x_1907_ = lean_unsigned_to_nat(1u);
v___x_1908_ = lean_nat_add(v_i_1849_, v___x_1907_);
lean_dec(v_i_1849_);
v___x_1909_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_1844_, v_k_1845_, v_ctorInfo_1846_, v_params_1847_, v_fields_1848_, v___x_1908_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1920_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_1920_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1920_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 1, v_a_1910_);
lean_ctor_set(v___x_1891_, 0, v_decl_1902_);
v___x_1915_ = v___x_1891_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_decl_1902_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1917_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v___x_1915_);
v___x_1917_ = v___x_1912_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_dec_ref_known(v_decl_1902_, 4);
lean_del_object(v___x_1891_);
return v___x_1909_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___y_1865_, 1);
lean_dec(v___y_1866_);
lean_dec(v_i_1849_);
lean_dec_ref(v_k_1845_);
lean_dec(v_discr_1844_);
v___y_1857_ = v_a_1850_;
v___y_1858_ = v_a_1851_;
v___y_1859_ = v_a_1852_;
v___y_1860_ = v_a_1853_;
v___y_1861_ = v_a_1854_;
goto v___jp_1856_;
}
}
}
v___jp_1925_:
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = lean_array_get_size(v_fields_1848_);
v___x_1928_ = lean_nat_dec_lt(v_i_1849_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_box(0);
v___y_1865_ = v___y_1926_;
v___y_1866_ = v___x_1929_;
goto v___jp_1864_;
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = lean_array_fget_borrowed(v_fields_1848_, v_i_1849_);
lean_inc(v___x_1930_);
v___x_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
v___y_1865_ = v___y_1926_;
v___y_1866_ = v___x_1931_;
goto v___jp_1864_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(lean_object* v_discr_1937_, lean_object* v_alt_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
if (lean_obj_tag(v_alt_1938_) == 0)
{
lean_object* v_ctorName_1945_; lean_object* v_params_1946_; lean_object* v_code_1947_; lean_object* v___x_1948_; 
v_ctorName_1945_ = lean_ctor_get(v_alt_1938_, 0);
lean_inc(v_ctorName_1945_);
v_params_1946_ = lean_ctor_get(v_alt_1938_, 1);
lean_inc_ref(v_params_1946_);
v_code_1947_ = lean_ctor_get(v_alt_1938_, 2);
lean_inc_ref(v_code_1947_);
lean_dec_ref_known(v_alt_1938_, 3);
v___x_1948_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_1945_, v_a_1942_, v_a_1943_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v_ctorInfo_1950_; lean_object* v_fieldInfo_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1976_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1948_, 1);
v_ctorInfo_1950_ = lean_ctor_get(v_a_1949_, 0);
v_fieldInfo_1951_ = lean_ctor_get(v_a_1949_, 1);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_a_1949_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1953_ = v_a_1949_;
v_isShared_1954_ = v_isSharedCheck_1976_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_fieldInfo_1951_);
lean_inc(v_ctorInfo_1950_);
lean_dec(v_a_1949_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1976_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_1956_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_1937_, v_code_1947_, v_ctorInfo_1950_, v_params_1946_, v_fieldInfo_1951_, v___x_1955_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec_ref(v_fieldInfo_1951_);
lean_dec_ref(v_params_1946_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1967_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1967_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1967_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set_tag(v___x_1953_, 1);
lean_ctor_set(v___x_1953_, 1, v_a_1957_);
v___x_1962_ = v___x_1953_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_ctorInfo_1950_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1964_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1962_);
v___x_1964_ = v___x_1959_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
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
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_del_object(v___x_1953_);
lean_dec_ref(v_ctorInfo_1950_);
v_a_1968_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1956_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1956_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec_ref(v_code_1947_);
lean_dec_ref(v_params_1946_);
lean_dec(v_discr_1937_);
v_a_1977_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1948_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1948_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
else
{
lean_object* v_code_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2009_; 
lean_dec(v_discr_1937_);
v_code_1985_ = lean_ctor_get(v_alt_1938_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_alt_1938_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1987_ = v_alt_1938_;
v_isShared_1988_ = v_isSharedCheck_2009_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_code_1985_);
lean_dec(v_alt_1938_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2009_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; 
v___x_1989_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_1985_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2000_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v_a_1990_);
v___x_1995_ = v___x_1987_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1997_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1995_);
v___x_1997_ = v___x_1992_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_del_object(v___x_1987_);
v_a_2001_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1989_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1989_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(lean_object* v_fvarId_2010_, size_t v_sz_2011_, size_t v_i_2012_, lean_object* v_bs_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
uint8_t v___x_2020_; 
v___x_2020_ = lean_usize_dec_lt(v_i_2012_, v_sz_2011_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
lean_dec(v_fvarId_2010_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_bs_2013_);
return v___x_2021_;
}
else
{
lean_object* v_v_2022_; lean_object* v___x_2023_; 
v_v_2022_ = lean_array_uget_borrowed(v_bs_2013_, v_i_2012_);
lean_inc(v_v_2022_);
lean_inc(v_fvarId_2010_);
v___x_2023_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_fvarId_2010_, v_v_2022_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; lean_object* v_bs_x27_2026_; size_t v___x_2027_; size_t v___x_2028_; lean_object* v___x_2029_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = lean_unsigned_to_nat(0u);
v_bs_x27_2026_ = lean_array_uset(v_bs_2013_, v_i_2012_, v___x_2025_);
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_add(v_i_2012_, v___x_2027_);
v___x_2029_ = lean_array_uset(v_bs_x27_2026_, v_i_2012_, v_a_2024_);
v_i_2012_ = v___x_2028_;
v_bs_2013_ = v___x_2029_;
goto _start;
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v_bs_2013_);
lean_dec(v_fvarId_2010_);
v_a_2031_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2023_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2023_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(lean_object* v_c_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
switch(lean_obj_tag(v_c_2039_))
{
case 0:
{
lean_object* v_decl_2046_; lean_object* v_k_2047_; lean_object* v___x_2048_; 
v_decl_2046_ = lean_ctor_get(v_c_2039_, 0);
lean_inc_ref(v_decl_2046_);
v_k_2047_ = lean_ctor_get(v_c_2039_, 1);
lean_inc_ref(v_k_2047_);
lean_dec_ref_known(v_c_2039_, 2);
v___x_2048_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2046_, v_k_2047_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
return v___x_2048_;
}
case 1:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_dec_ref_known(v_c_2039_, 2);
v___x_2049_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2);
v___x_2050_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2049_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
return v___x_2050_;
}
case 2:
{
lean_object* v_decl_2051_; lean_object* v_k_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2144_; 
v_decl_2051_ = lean_ctor_get(v_c_2039_, 0);
v_k_2052_ = lean_ctor_get(v_c_2039_, 1);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_c_2039_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2054_ = v_c_2039_;
v_isShared_2055_ = v_isSharedCheck_2144_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_k_2052_);
lean_inc(v_decl_2051_);
lean_dec(v_c_2039_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2144_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_fvarId_2056_; lean_object* v_binderName_2057_; lean_object* v_params_2058_; lean_object* v_type_2059_; lean_object* v_value_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2143_; 
v_fvarId_2056_ = lean_ctor_get(v_decl_2051_, 0);
v_binderName_2057_ = lean_ctor_get(v_decl_2051_, 1);
v_params_2058_ = lean_ctor_get(v_decl_2051_, 2);
v_type_2059_ = lean_ctor_get(v_decl_2051_, 3);
v_value_2060_ = lean_ctor_get(v_decl_2051_, 4);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_decl_2051_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2062_ = v_decl_2051_;
v_isShared_2063_ = v_isSharedCheck_2143_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_value_2060_);
lean_inc(v_type_2059_);
lean_inc(v_params_2058_);
lean_inc(v_binderName_2057_);
lean_inc(v_fvarId_2056_);
lean_dec(v_decl_2051_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2143_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
size_t v_sz_2064_; size_t v___x_2065_; lean_object* v___x_2066_; 
v_sz_2064_ = lean_array_size(v_params_2058_);
v___x_2065_ = ((size_t)0ULL);
v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2064_, v___x_2065_, v_params_2058_, v_a_2040_, v_a_2042_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2068_; lean_object* v_subst_2069_; lean_object* v_jpParamMask_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2134_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
v___x_2068_ = lean_st_ref_take(v_a_2040_);
v_subst_2069_ = lean_ctor_get(v___x_2068_, 0);
v_jpParamMask_2070_ = lean_ctor_get(v___x_2068_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2072_ = v___x_2068_;
v_isShared_2073_ = v_isSharedCheck_2134_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_jpParamMask_2070_);
lean_inc(v_subst_2069_);
lean_dec(v___x_2068_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2134_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
size_t v_sz_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
v_sz_2074_ = lean_array_size(v_a_2067_);
lean_inc(v_a_2067_);
v___x_2075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_2074_, v___x_2065_, v_a_2067_);
lean_inc_ref(v___x_2075_);
lean_inc(v_fvarId_2056_);
v___x_2076_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_jpParamMask_2070_, v_fvarId_2056_, v___x_2075_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 1, v___x_2076_);
v___x_2078_ = v___x_2072_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_subst_2069_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; lean_object* v___y_2081_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2079_ = lean_st_ref_put(v_a_2040_, v___x_2078_);
v___x_2123_ = lean_unsigned_to_nat(0u);
v___x_2124_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3));
v___x_2125_ = l_Array_zip___redArg(v_a_2067_, v___x_2075_);
lean_dec_ref(v___x_2075_);
v___x_2126_ = lean_array_get_size(v___x_2125_);
v___x_2127_ = lean_nat_dec_lt(v___x_2123_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_dec_ref(v___x_2125_);
v___y_2081_ = v___x_2124_;
goto v___jp_2080_;
}
else
{
uint8_t v___x_2128_; 
v___x_2128_ = lean_nat_dec_le(v___x_2126_, v___x_2126_);
if (v___x_2128_ == 0)
{
if (v___x_2127_ == 0)
{
lean_dec_ref(v___x_2125_);
v___y_2081_ = v___x_2124_;
goto v___jp_2080_;
}
else
{
size_t v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_usize_of_nat(v___x_2126_);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2125_, v___x_2065_, v___x_2129_, v___x_2124_);
lean_dec_ref(v___x_2125_);
v___y_2081_ = v___x_2130_;
goto v___jp_2080_;
}
}
else
{
size_t v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_usize_of_nat(v___x_2126_);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2125_, v___x_2065_, v___x_2131_, v___x_2124_);
lean_dec_ref(v___x_2125_);
v___y_2081_ = v___x_2132_;
goto v___jp_2080_;
}
}
v___jp_2080_:
{
lean_object* v___x_2082_; 
v___x_2082_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_value_2060_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2084_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v___x_2084_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2052_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___x_2084_, 1);
v___x_2086_ = lean_array_get_size(v_a_2067_);
lean_dec(v_a_2067_);
v___x_2087_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2059_, v___x_2086_, v_a_2043_, v_a_2044_);
lean_dec_ref(v_type_2059_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2114_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2114_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2114_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v_lctx_2093_; lean_object* v_nextIdx_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2113_; 
v___x_2092_ = lean_st_ref_take(v_a_2042_);
v_lctx_2093_ = lean_ctor_get(v___x_2092_, 0);
v_nextIdx_2094_ = lean_ctor_get(v___x_2092_, 1);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2096_ = v___x_2092_;
v_isShared_2097_ = v_isSharedCheck_2113_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_nextIdx_2094_);
lean_inc(v_lctx_2093_);
lean_dec(v___x_2092_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2113_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
uint8_t v___x_2098_; lean_object* v___x_2100_; 
v___x_2098_ = 1;
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 4, v_a_2083_);
lean_ctor_set(v___x_2062_, 3, v_a_2088_);
lean_ctor_set(v___x_2062_, 2, v___y_2081_);
v___x_2100_ = v___x_2062_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_fvarId_2056_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_binderName_2057_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v___y_2081_);
lean_ctor_set(v_reuseFailAlloc_2112_, 3, v_a_2088_);
lean_ctor_set(v_reuseFailAlloc_2112_, 4, v_a_2083_);
v___x_2100_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2103_; 
lean_inc_ref(v___x_2100_);
v___x_2101_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2098_, v_lctx_2093_, v___x_2100_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2101_);
v___x_2103_ = v___x_2096_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_nextIdx_2094_);
v___x_2103_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = lean_st_ref_put(v_a_2042_, v___x_2103_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 1, v_a_2085_);
lean_ctor_set(v___x_2054_, 0, v___x_2100_);
v___x_2106_ = v___x_2054_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_a_2085_);
v___x_2106_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2106_);
v___x_2108_ = v___x_2090_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec(v_a_2085_);
lean_dec(v_a_2083_);
lean_dec_ref(v___y_2081_);
lean_del_object(v___x_2062_);
lean_dec(v_binderName_2057_);
lean_dec(v_fvarId_2056_);
lean_del_object(v___x_2054_);
v_a_2115_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2087_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2087_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
else
{
lean_dec(v_a_2083_);
lean_dec_ref(v___y_2081_);
lean_dec(v_a_2067_);
lean_del_object(v___x_2062_);
lean_dec_ref(v_type_2059_);
lean_dec(v_binderName_2057_);
lean_dec(v_fvarId_2056_);
lean_del_object(v___x_2054_);
return v___x_2084_;
}
}
else
{
lean_dec_ref(v___y_2081_);
lean_dec(v_a_2067_);
lean_del_object(v___x_2062_);
lean_dec_ref(v_type_2059_);
lean_dec(v_binderName_2057_);
lean_dec(v_fvarId_2056_);
lean_del_object(v___x_2054_);
lean_dec_ref(v_k_2052_);
return v___x_2082_;
}
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_del_object(v___x_2062_);
lean_dec_ref(v_value_2060_);
lean_dec_ref(v_type_2059_);
lean_dec(v_binderName_2057_);
lean_dec(v_fvarId_2056_);
lean_del_object(v___x_2054_);
lean_dec_ref(v_k_2052_);
v_a_2135_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2066_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2066_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2145_; lean_object* v_args_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2182_; 
v_fvarId_2145_ = lean_ctor_get(v_c_2039_, 0);
v_args_2146_ = lean_ctor_get(v_c_2039_, 1);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_c_2039_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2148_ = v_c_2039_;
v_isShared_2149_ = v_isSharedCheck_2182_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_args_2146_);
lean_inc(v_fvarId_2145_);
lean_dec(v_c_2039_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2182_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_a_2151_; lean_object* v___y_2157_; lean_object* v___x_2167_; lean_object* v_jpParamMask_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2167_ = lean_st_ref_get(v_a_2040_);
v_jpParamMask_2168_ = lean_ctor_get(v___x_2167_, 1);
lean_inc_ref(v_jpParamMask_2168_);
lean_dec(v___x_2167_);
v___x_2169_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_jpParamMask_2168_, v_fvarId_2145_);
lean_dec_ref(v_jpParamMask_2168_);
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_2172_ = l_Array_zip___redArg(v_args_2146_, v___x_2169_);
lean_dec_ref(v___x_2169_);
lean_dec_ref(v_args_2146_);
v___x_2173_ = lean_array_get_size(v___x_2172_);
v___x_2174_ = lean_nat_dec_lt(v___x_2170_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_dec_ref(v___x_2172_);
v_a_2151_ = v___x_2171_;
goto v___jp_2150_;
}
else
{
uint8_t v___x_2175_; 
v___x_2175_ = lean_nat_dec_le(v___x_2173_, v___x_2173_);
if (v___x_2175_ == 0)
{
if (v___x_2174_ == 0)
{
lean_dec_ref(v___x_2172_);
v_a_2151_ = v___x_2171_;
goto v___jp_2150_;
}
else
{
size_t v___x_2176_; size_t v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = ((size_t)0ULL);
v___x_2177_ = lean_usize_of_nat(v___x_2173_);
v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2172_, v___x_2176_, v___x_2177_, v___x_2171_, v_a_2040_);
lean_dec_ref(v___x_2172_);
v___y_2157_ = v___x_2178_;
goto v___jp_2156_;
}
}
else
{
size_t v___x_2179_; size_t v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = ((size_t)0ULL);
v___x_2180_ = lean_usize_of_nat(v___x_2173_);
v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2172_, v___x_2179_, v___x_2180_, v___x_2171_, v_a_2040_);
lean_dec_ref(v___x_2172_);
v___y_2157_ = v___x_2181_;
goto v___jp_2156_;
}
}
v___jp_2150_:
{
lean_object* v___x_2153_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v_a_2151_);
v___x_2153_ = v___x_2148_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_fvarId_2145_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_a_2151_);
v___x_2153_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2154_; 
v___x_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
return v___x_2154_;
}
}
v___jp_2156_:
{
if (lean_obj_tag(v___y_2157_) == 0)
{
lean_object* v_a_2158_; 
v_a_2158_ = lean_ctor_get(v___y_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___y_2157_, 1);
v_a_2151_ = v_a_2158_;
goto v___jp_2150_;
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_del_object(v___x_2148_);
lean_dec(v_fvarId_2145_);
v_a_2159_ = lean_ctor_get(v___y_2157_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___y_2157_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___y_2157_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___y_2157_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
}
case 4:
{
lean_object* v_cases_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2293_; 
v_cases_2183_ = lean_ctor_get(v_c_2039_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_c_2039_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2185_ = v_c_2039_;
v_isShared_2186_ = v_isSharedCheck_2293_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_cases_2183_);
lean_dec(v_c_2039_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2293_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v_typeName_2187_; lean_object* v_resultType_2188_; lean_object* v_discr_2189_; lean_object* v_alts_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2292_; 
v_typeName_2187_ = lean_ctor_get(v_cases_2183_, 0);
v_resultType_2188_ = lean_ctor_get(v_cases_2183_, 1);
v_discr_2189_ = lean_ctor_get(v_cases_2183_, 2);
v_alts_2190_ = lean_ctor_get(v_cases_2183_, 3);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_cases_2183_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2192_ = v_cases_2183_;
v_isShared_2193_ = v_isSharedCheck_2292_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_alts_2190_);
lean_inc(v_discr_2189_);
lean_inc(v_resultType_2188_);
lean_inc(v_typeName_2187_);
lean_dec(v_cases_2183_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2292_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; 
lean_inc(v_typeName_2187_);
v___x_2194_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_2187_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
if (lean_obj_tag(v_a_2195_) == 1)
{
lean_object* v_val_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
lean_del_object(v___x_2192_);
lean_dec_ref(v_resultType_2188_);
lean_dec(v_typeName_2187_);
lean_del_object(v___x_2185_);
v_val_2196_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_val_2196_);
lean_dec_ref_known(v_a_2195_, 1);
v___x_2197_ = lean_array_get_size(v_alts_2190_);
v___x_2198_ = lean_unsigned_to_nat(1u);
v___x_2199_ = lean_nat_dec_eq(v___x_2197_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_dec(v_val_2196_);
lean_dec_ref(v_alts_2190_);
lean_dec(v_discr_2189_);
v___x_2200_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6);
v___x_2201_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2200_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
return v___x_2201_;
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7);
v___x_2203_ = lean_unsigned_to_nat(0u);
v___x_2204_ = lean_array_get(v___x_2202_, v_alts_2190_, v___x_2203_);
lean_dec_ref(v_alts_2190_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_ctorName_2205_; lean_object* v_params_2206_; lean_object* v_code_2207_; lean_object* v_ctorName_2208_; lean_object* v_fieldIdx_2209_; uint8_t v___x_2210_; 
v_ctorName_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_ctorName_2205_);
v_params_2206_ = lean_ctor_get(v___x_2204_, 1);
lean_inc_ref(v_params_2206_);
v_code_2207_ = lean_ctor_get(v___x_2204_, 2);
lean_inc_ref(v_code_2207_);
lean_dec_ref_known(v___x_2204_, 3);
v_ctorName_2208_ = lean_ctor_get(v_val_2196_, 0);
lean_inc(v_ctorName_2208_);
v_fieldIdx_2209_ = lean_ctor_get(v_val_2196_, 2);
lean_inc(v_fieldIdx_2209_);
lean_dec(v_val_2196_);
v___x_2210_ = lean_name_eq(v_ctorName_2205_, v_ctorName_2208_);
lean_dec(v_ctorName_2208_);
lean_dec(v_ctorName_2205_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
lean_dec(v_fieldIdx_2209_);
lean_dec_ref(v_code_2207_);
lean_dec_ref(v_params_2206_);
lean_dec(v_discr_2189_);
v___x_2211_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9);
v___x_2212_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2211_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
return v___x_2212_;
}
else
{
lean_object* v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = lean_array_get_size(v_params_2206_);
v___x_2214_ = lean_nat_dec_lt(v_fieldIdx_2209_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec(v_fieldIdx_2209_);
lean_dec_ref(v_code_2207_);
lean_dec_ref(v_params_2206_);
lean_dec(v_discr_2189_);
v___x_2215_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11);
v___x_2216_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2215_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
return v___x_2216_;
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = lean_box(0);
v___x_2218_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v___x_2213_, v_params_2206_, v_fieldIdx_2209_, v_discr_2189_, v___x_2203_, v___x_2217_, v_a_2040_);
lean_dec(v_fieldIdx_2209_);
lean_dec_ref(v_params_2206_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_dec_ref_known(v___x_2218_, 1);
v_c_2039_ = v_code_2207_;
goto _start;
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec_ref(v_code_2207_);
v_a_2220_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2218_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2218_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec(v___x_2204_);
lean_dec(v_val_2196_);
lean_dec(v_discr_2189_);
v___x_2228_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13);
v___x_2229_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2228_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
return v___x_2229_;
}
}
}
else
{
lean_object* v___x_2230_; lean_object* v_subst_2231_; uint8_t v___x_2232_; lean_object* v___x_2233_; 
lean_dec(v_a_2195_);
v___x_2230_ = lean_st_ref_get(v_a_2040_);
v_subst_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc_ref(v_subst_2231_);
lean_dec(v___x_2230_);
v___x_2232_ = 1;
v___x_2233_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2231_, v_discr_2189_, v___x_2232_);
lean_dec_ref(v_subst_2231_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_fvarId_2234_; lean_object* v___x_2235_; 
v_fvarId_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_fvarId_2234_);
lean_dec_ref_known(v___x_2233_, 1);
v___x_2235_ = l_Lean_Compiler_LCNF_toImpureType(v_resultType_2188_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; size_t v_sz_2237_; size_t v___x_2238_; lean_object* v___x_2239_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
v_sz_2237_ = lean_array_size(v_alts_2190_);
v___x_2238_ = ((size_t)0ULL);
lean_inc(v_fvarId_2234_);
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2234_, v_sz_2237_, v___x_2238_, v_alts_2190_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2241_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v___x_2241_ = l_Lean_Compiler_LCNF_nameToImpureType(v_typeName_2187_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2257_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2257_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2257_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2246_ = l_Lean_Expr_getAppFn(v_a_2242_);
lean_dec(v_a_2242_);
v___x_2247_ = l_Lean_Expr_constName_x21(v___x_2246_);
lean_dec_ref(v___x_2246_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 3, v_a_2240_);
lean_ctor_set(v___x_2192_, 2, v_fvarId_2234_);
lean_ctor_set(v___x_2192_, 1, v_a_2236_);
lean_ctor_set(v___x_2192_, 0, v___x_2247_);
v___x_2249_ = v___x_2192_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_a_2236_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v_fvarId_2234_);
lean_ctor_set(v_reuseFailAlloc_2256_, 3, v_a_2240_);
v___x_2249_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2251_; 
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2249_);
v___x_2251_ = v___x_2185_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2251_);
v___x_2253_ = v___x_2244_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v_a_2240_);
lean_dec(v_a_2236_);
lean_dec(v_fvarId_2234_);
lean_del_object(v___x_2192_);
lean_del_object(v___x_2185_);
v_a_2258_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2241_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2241_);
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
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_a_2236_);
lean_dec(v_fvarId_2234_);
lean_del_object(v___x_2192_);
lean_dec(v_typeName_2187_);
lean_del_object(v___x_2185_);
v_a_2266_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2239_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2239_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
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
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_fvarId_2234_);
lean_del_object(v___x_2192_);
lean_dec_ref(v_alts_2190_);
lean_dec(v_typeName_2187_);
lean_del_object(v___x_2185_);
v_a_2274_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2235_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2235_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
uint8_t v___x_2282_; lean_object* v___x_2283_; 
lean_del_object(v___x_2192_);
lean_dec_ref(v_alts_2190_);
lean_dec_ref(v_resultType_2188_);
lean_dec(v_typeName_2187_);
lean_del_object(v___x_2185_);
v___x_2282_ = 1;
v___x_2283_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2282_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
return v___x_2283_;
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_del_object(v___x_2192_);
lean_dec_ref(v_alts_2190_);
lean_dec(v_discr_2189_);
lean_dec_ref(v_resultType_2188_);
lean_dec(v_typeName_2187_);
lean_del_object(v___x_2185_);
v_a_2284_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2194_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2194_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2315_; 
v_fvarId_2294_ = lean_ctor_get(v_c_2039_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_c_2039_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2296_ = v_c_2039_;
v_isShared_2297_ = v_isSharedCheck_2315_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_fvarId_2294_);
lean_dec(v_c_2039_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2315_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v_subst_2299_; uint8_t v___x_2300_; lean_object* v___x_2301_; 
v___x_2298_ = lean_st_ref_get(v_a_2040_);
v_subst_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc_ref(v_subst_2299_);
lean_dec(v___x_2298_);
v___x_2300_ = 1;
v___x_2301_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2299_, v_fvarId_2294_, v___x_2300_);
lean_dec_ref(v_subst_2299_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_fvarId_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2312_; 
v_fvarId_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2312_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_fvarId_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2312_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v_fvarId_2302_);
v___x_2307_ = v___x_2296_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_fvarId_2302_);
v___x_2307_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2309_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2307_);
v___x_2309_ = v___x_2304_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
else
{
uint8_t v___x_2313_; lean_object* v___x_2314_; 
lean_del_object(v___x_2296_);
v___x_2313_ = 1;
v___x_2314_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2313_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
return v___x_2314_;
}
}
}
default: 
{
lean_object* v_type_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2340_; 
v_type_2316_ = lean_ctor_get(v_c_2039_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_c_2039_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2318_ = v_c_2039_;
v_isShared_2319_ = v_isSharedCheck_2340_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_type_2316_);
lean_dec(v_c_2039_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2340_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_Compiler_LCNF_toImpureType(v_type_2316_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2331_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2331_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2331_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v_a_2321_);
v___x_2326_ = v___x_2318_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2321_);
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
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_del_object(v___x_2318_);
v_a_2332_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2320_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2320_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(lean_object* v_decl_2341_, lean_object* v_k_2342_, lean_object* v_ctorInfo_2343_, lean_object* v_fields_2344_, lean_object* v_irArgs_2345_, lean_object* v_i_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2353_ = lean_array_get_size(v_irArgs_2345_);
v___x_2354_ = lean_nat_dec_lt(v_i_2346_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; 
lean_dec(v_i_2346_);
lean_dec_ref(v_decl_2341_);
v___x_2355_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2342_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
return v___x_2355_;
}
else
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_array_fget_borrowed(v_irArgs_2345_, v_i_2346_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_unsigned_to_nat(1u);
v___x_2358_ = lean_nat_add(v_i_2346_, v___x_2357_);
lean_dec(v_i_2346_);
v_i_2346_ = v___x_2358_;
goto _start;
}
else
{
lean_object* v_fvarId_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_fvarId_2360_ = lean_ctor_get(v___x_2356_, 0);
v___x_2361_ = lean_box(0);
v___x_2362_ = lean_array_get_borrowed(v___x_2361_, v_fields_2344_, v_i_2346_);
switch(lean_obj_tag(v___x_2362_))
{
case 1:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = lean_nat_add(v_i_2346_, v___x_2363_);
lean_dec(v_i_2346_);
v_i_2346_ = v___x_2364_;
goto _start;
}
case 2:
{
lean_object* v_i_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_i_2366_ = lean_ctor_get(v___x_2362_, 0);
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = lean_nat_add(v_i_2346_, v___x_2367_);
lean_dec(v_i_2346_);
lean_inc_ref(v_decl_2341_);
v___x_2369_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2341_, v_k_2342_, v_ctorInfo_2343_, v_fields_2344_, v_irArgs_2345_, v___x_2368_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2388_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2388_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2388_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v_fvarId_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2384_; 
v_fvarId_2374_ = lean_ctor_get(v_decl_2341_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_decl_2341_);
if (v_isSharedCheck_2384_ == 0)
{
lean_object* v_unused_2385_; lean_object* v_unused_2386_; lean_object* v_unused_2387_; 
v_unused_2385_ = lean_ctor_get(v_decl_2341_, 3);
lean_dec(v_unused_2385_);
v_unused_2386_ = lean_ctor_get(v_decl_2341_, 2);
lean_dec(v_unused_2386_);
v_unused_2387_ = lean_ctor_get(v_decl_2341_, 1);
lean_dec(v_unused_2387_);
v___x_2376_ = v_decl_2341_;
v_isShared_2377_ = v_isSharedCheck_2384_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_fvarId_2374_);
lean_dec(v_decl_2341_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2384_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
lean_inc(v_fvarId_2360_);
lean_inc(v_i_2366_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set_tag(v___x_2376_, 8);
lean_ctor_set(v___x_2376_, 3, v_a_2370_);
lean_ctor_set(v___x_2376_, 2, v_fvarId_2360_);
lean_ctor_set(v___x_2376_, 1, v_i_2366_);
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_fvarId_2374_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v_i_2366_);
lean_ctor_set(v_reuseFailAlloc_2383_, 2, v_fvarId_2360_);
lean_ctor_set(v_reuseFailAlloc_2383_, 3, v_a_2370_);
v___x_2379_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2381_; 
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2379_);
v___x_2381_ = v___x_2372_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_2341_);
return v___x_2369_;
}
}
case 3:
{
lean_object* v_offset_2389_; lean_object* v_type_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_offset_2389_ = lean_ctor_get(v___x_2362_, 1);
v_type_2390_ = lean_ctor_get(v___x_2362_, 2);
v___x_2391_ = lean_unsigned_to_nat(1u);
v___x_2392_ = lean_nat_add(v_i_2346_, v___x_2391_);
lean_dec(v_i_2346_);
lean_inc_ref(v_decl_2341_);
v___x_2393_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2341_, v_k_2342_, v_ctorInfo_2343_, v_fields_2344_, v_irArgs_2345_, v___x_2392_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2406_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2396_ = v___x_2393_;
v_isShared_2397_ = v_isSharedCheck_2406_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2406_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_fvarId_2398_; lean_object* v_size_2399_; lean_object* v_usize_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v_fvarId_2398_ = lean_ctor_get(v_decl_2341_, 0);
lean_inc(v_fvarId_2398_);
lean_dec_ref(v_decl_2341_);
v_size_2399_ = lean_ctor_get(v_ctorInfo_2343_, 2);
v_usize_2400_ = lean_ctor_get(v_ctorInfo_2343_, 3);
v___x_2401_ = lean_nat_add(v_size_2399_, v_usize_2400_);
lean_inc_ref(v_type_2390_);
lean_inc(v_fvarId_2360_);
lean_inc(v_offset_2389_);
v___x_2402_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_2402_, 0, v_fvarId_2398_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
lean_ctor_set(v___x_2402_, 2, v_offset_2389_);
lean_ctor_set(v___x_2402_, 3, v_fvarId_2360_);
lean_ctor_set(v___x_2402_, 4, v_type_2390_);
lean_ctor_set(v___x_2402_, 5, v_a_2394_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2402_);
v___x_2404_ = v___x_2396_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
else
{
lean_dec_ref(v_decl_2341_);
return v___x_2393_;
}
}
default: 
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_unsigned_to_nat(1u);
v___x_2408_ = lean_nat_add(v_i_2346_, v___x_2407_);
lean_dec(v_i_2346_);
v_i_2346_ = v___x_2408_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(lean_object* v_decl_2410_, lean_object* v_k_2411_, lean_object* v_ctorInfo_2412_, lean_object* v_fields_2413_, lean_object* v_irArgs_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2410_, v_k_2411_, v_ctorInfo_2412_, v_fields_2413_, v_irArgs_2414_, v___x_2421_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(lean_object* v_decl_2423_, lean_object* v_k_2424_, lean_object* v_ctorInfo_2425_, lean_object* v_fields_2426_, lean_object* v_irArgs_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_2423_, v_k_2424_, v_ctorInfo_2425_, v_fields_2426_, v_irArgs_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec_ref(v_irArgs_2427_);
lean_dec_ref(v_fields_2426_);
lean_dec_ref(v_ctorInfo_2425_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(lean_object* v_decl_2435_, lean_object* v_k_2436_, lean_object* v_name_2437_, lean_object* v_args_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_2435_, v_k_2436_, v_name_2437_, v_args_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(lean_object* v_decl_2446_, lean_object* v_k_2447_, lean_object* v_name_2448_, lean_object* v_args_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_2446_, v_k_2447_, v_name_2448_, v_args_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object* v_k_2457_, lean_object* v_fvarId_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_2457_, v_fvarId_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object* v_decl_2466_, lean_object* v_k_2467_, lean_object* v_name_2468_, lean_object* v_numParams_2469_, lean_object* v_args_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_2466_, v_k_2467_, v_name_2468_, v_numParams_2469_, v_args_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object* v_fvarId_2478_, lean_object* v_sz_2479_, lean_object* v_i_2480_, lean_object* v_bs_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
size_t v_sz_boxed_2488_; size_t v_i_boxed_2489_; lean_object* v_res_2490_; 
v_sz_boxed_2488_ = lean_unbox_usize(v_sz_2479_);
lean_dec(v_sz_2479_);
v_i_boxed_2489_ = lean_unbox_usize(v_i_2480_);
lean_dec(v_i_2480_);
v_res_2490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2478_, v_sz_boxed_2488_, v_i_boxed_2489_, v_bs_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object* v_k_2491_, lean_object* v_decl_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_2491_, v_decl_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object* v_discr_2500_, lean_object* v_alt_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_discr_2500_, v_alt_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object* v_decl_2509_, lean_object* v_k_2510_, lean_object* v_name_2511_, lean_object* v_numParams_2512_, lean_object* v_args_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_2509_, v_k_2510_, v_name_2511_, v_numParams_2512_, v_args_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_a_2514_);
lean_dec_ref(v_args_2513_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* v_decl_2521_, lean_object* v_k_2522_, lean_object* v_ctorInfo_2523_, lean_object* v_fields_2524_, lean_object* v_irArgs_2525_, lean_object* v_i_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2521_, v_k_2522_, v_ctorInfo_2523_, v_fields_2524_, v_irArgs_2525_, v_i_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec_ref(v_irArgs_2525_);
lean_dec_ref(v_fields_2524_);
lean_dec_ref(v_ctorInfo_2523_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(lean_object* v_discr_2534_, lean_object* v_k_2535_, lean_object* v_ctorInfo_2536_, lean_object* v_params_2537_, lean_object* v_fields_2538_, lean_object* v_i_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2534_, v_k_2535_, v_ctorInfo_2536_, v_params_2537_, v_fields_2538_, v_i_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_fields_2538_);
lean_dec_ref(v_params_2537_);
lean_dec_ref(v_ctorInfo_2536_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(lean_object* v_c_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_c_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
lean_dec(v_a_2548_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(lean_object* v_decl_2555_, lean_object* v_k_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2555_, v_k_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(lean_object* v_00_u03b1_2564_, lean_object* v_msg_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_2565_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(lean_object* v_00_u03b1_2573_, lean_object* v_msg_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(v_00_u03b1_2573_, v_msg_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(size_t v_sz_2582_, size_t v_i_2583_, lean_object* v_bs_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2582_, v_i_2583_, v_bs_2584_, v___y_2585_, v___y_2587_, v___y_2588_, v___y_2589_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(lean_object* v_sz_2592_, lean_object* v_i_2593_, lean_object* v_bs_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
size_t v_sz_boxed_2601_; size_t v_i_boxed_2602_; lean_object* v_res_2603_; 
v_sz_boxed_2601_ = lean_unbox_usize(v_sz_2592_);
lean_dec(v_sz_2592_);
v_i_boxed_2602_ = lean_unbox_usize(v_i_2593_);
lean_dec(v_i_2593_);
v_res_2603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(v_sz_boxed_2601_, v_i_boxed_2602_, v_bs_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(lean_object* v_as_2604_, size_t v_i_2605_, size_t v_stop_2606_, lean_object* v_b_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_2604_, v_i_2605_, v_stop_2606_, v_b_2607_, v___y_2608_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(lean_object* v_as_2615_, lean_object* v_i_2616_, lean_object* v_stop_2617_, lean_object* v_b_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
size_t v_i_boxed_2625_; size_t v_stop_boxed_2626_; lean_object* v_res_2627_; 
v_i_boxed_2625_ = lean_unbox_usize(v_i_2616_);
lean_dec(v_i_2616_);
v_stop_boxed_2626_ = lean_unbox_usize(v_stop_2617_);
lean_dec(v_stop_2617_);
v_res_2627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(v_as_2615_, v_i_boxed_2625_, v_stop_boxed_2626_, v_b_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v_as_2615_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(lean_object* v_upperBound_2628_, lean_object* v_params_2629_, lean_object* v___x_2630_, lean_object* v_discr_2631_, lean_object* v_inst_2632_, lean_object* v_R_2633_, lean_object* v_a_2634_, lean_object* v_b_2635_, lean_object* v_c_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_2628_, v_params_2629_, v___x_2630_, v_discr_2631_, v_a_2634_, v_b_2635_, v___y_2637_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(lean_object* v_upperBound_2644_, lean_object* v_params_2645_, lean_object* v___x_2646_, lean_object* v_discr_2647_, lean_object* v_inst_2648_, lean_object* v_R_2649_, lean_object* v_a_2650_, lean_object* v_b_2651_, lean_object* v_c_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(v_upperBound_2644_, v_params_2645_, v___x_2646_, v_discr_2647_, v_inst_2648_, v_R_2649_, v_a_2650_, v_b_2651_, v_c_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec(v___x_2646_);
lean_dec_ref(v_params_2645_);
lean_dec(v_upperBound_2644_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(size_t v_sz_2660_, size_t v_i_2661_, lean_object* v_bs_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_2660_, v_i_2661_, v_bs_2662_, v___y_2663_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___boxed(lean_object* v_sz_2670_, lean_object* v_i_2671_, lean_object* v_bs_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
size_t v_sz_boxed_2679_; size_t v_i_boxed_2680_; lean_object* v_res_2681_; 
v_sz_boxed_2679_ = lean_unbox_usize(v_sz_2670_);
lean_dec(v_sz_2670_);
v_i_boxed_2680_ = lean_unbox_usize(v_i_2671_);
lean_dec(v_i_2671_);
v_res_2681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(v_sz_boxed_2679_, v_i_boxed_2680_, v_bs_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(lean_object* v_upperBound_2682_, lean_object* v_fieldInfo_2683_, lean_object* v___x_2684_, lean_object* v_inst_2685_, lean_object* v_R_2686_, lean_object* v_a_2687_, lean_object* v_b_2688_, lean_object* v_c_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_2682_, v_fieldInfo_2683_, v___x_2684_, v_a_2687_, v_b_2688_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(lean_object* v_upperBound_2697_, lean_object* v_fieldInfo_2698_, lean_object* v___x_2699_, lean_object* v_inst_2700_, lean_object* v_R_2701_, lean_object* v_a_2702_, lean_object* v_b_2703_, lean_object* v_c_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(v_upperBound_2697_, v_fieldInfo_2698_, v___x_2699_, v_inst_2700_, v_R_2701_, v_a_2702_, v_b_2703_, v_c_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___x_2699_);
lean_dec_ref(v_fieldInfo_2698_);
lean_dec(v_upperBound_2697_);
return v_res_2711_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0));
v___x_2714_ = l_Lean_stringToMessageData(v___x_2713_);
return v___x_2714_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2));
v___x_2717_ = l_Lean_stringToMessageData(v___x_2716_);
return v___x_2717_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4));
v___x_2720_ = l_Lean_stringToMessageData(v___x_2719_);
return v___x_2720_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6));
v___x_2723_ = l_Lean_stringToMessageData(v___x_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(lean_object* v_decl_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v_toSignature_2731_; lean_object* v_value_2732_; uint8_t v_recursive_2733_; lean_object* v_inlineAttr_x3f_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2866_; 
v_toSignature_2731_ = lean_ctor_get(v_decl_2724_, 0);
v_value_2732_ = lean_ctor_get(v_decl_2724_, 1);
v_recursive_2733_ = lean_ctor_get_uint8(v_decl_2724_, sizeof(void*)*3);
v_inlineAttr_x3f_2734_ = lean_ctor_get(v_decl_2724_, 2);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_decl_2724_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2736_ = v_decl_2724_;
v_isShared_2737_ = v_isSharedCheck_2866_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_inlineAttr_x3f_2734_);
lean_inc(v_value_2732_);
lean_inc(v_toSignature_2731_);
lean_dec(v_decl_2724_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2866_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v_name_2738_; lean_object* v_levelParams_2739_; lean_object* v_type_2740_; lean_object* v_params_2741_; uint8_t v_safe_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2865_; 
v_name_2738_ = lean_ctor_get(v_toSignature_2731_, 0);
v_levelParams_2739_ = lean_ctor_get(v_toSignature_2731_, 1);
v_type_2740_ = lean_ctor_get(v_toSignature_2731_, 2);
v_params_2741_ = lean_ctor_get(v_toSignature_2731_, 3);
v_safe_2742_ = lean_ctor_get_uint8(v_toSignature_2731_, sizeof(void*)*4);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_toSignature_2731_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2744_ = v_toSignature_2731_;
v_isShared_2745_ = v_isSharedCheck_2865_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_params_2741_);
lean_inc(v_type_2740_);
lean_inc(v_levelParams_2739_);
lean_inc(v_name_2738_);
lean_dec(v_toSignature_2731_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2865_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
size_t v_sz_2746_; size_t v___x_2747_; lean_object* v___x_2748_; 
v_sz_2746_ = lean_array_size(v_params_2741_);
v___x_2747_ = ((size_t)0ULL);
lean_inc_ref(v_params_2741_);
v___x_2748_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2746_, v___x_2747_, v_params_2741_, v_a_2725_, v_a_2727_, v_a_2728_, v_a_2729_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2750_ = lean_array_get_size(v_params_2741_);
lean_dec_ref(v_params_2741_);
v___x_2751_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2740_, v___x_2750_, v_a_2728_, v_a_2729_);
lean_dec_ref(v_type_2740_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2848_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2848_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2848_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v_env_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v___x_2756_ = lean_st_ref_get(v_a_2729_);
v_env_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc_ref(v_env_2757_);
lean_dec(v___x_2756_);
v___x_2758_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
lean_inc(v_name_2738_);
v___x_2759_ = l_Lean_TagAttribute_hasTag(v___x_2758_, v_env_2757_, v_name_2738_);
if (lean_obj_tag(v_value_2732_) == 0)
{
lean_object* v_code_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2810_; 
lean_del_object(v___x_2754_);
v_code_2760_ = lean_ctor_get(v_value_2732_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v_value_2732_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2762_ = v_value_2732_;
v_isShared_2763_ = v_isSharedCheck_2810_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_code_2760_);
lean_dec(v_value_2732_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2810_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; 
if (v___x_2759_ == 0)
{
v___y_2765_ = v_a_2725_;
v___y_2766_ = v_a_2726_;
v___y_2767_ = v_a_2727_;
v___y_2768_ = v_a_2728_;
v___y_2769_ = v_a_2729_;
goto v___jp_2764_;
}
else
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_del_object(v___x_2762_);
lean_dec_ref(v_code_2760_);
lean_dec(v_a_2752_);
lean_dec(v_a_2749_);
lean_del_object(v___x_2744_);
lean_dec(v_levelParams_2739_);
lean_del_object(v___x_2736_);
lean_dec(v_inlineAttr_x3f_2734_);
v___x_2796_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1);
v___x_2797_ = l_Lean_MessageData_ofName(v_name_2738_);
v___x_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2796_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2800_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
v___jp_2764_:
{
lean_object* v___x_2770_; 
v___x_2770_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_2760_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2787_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2787_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2787_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 3, v_a_2749_);
lean_ctor_set(v___x_2744_, 2, v_a_2752_);
v___x_2776_ = v___x_2744_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_name_2738_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_levelParams_2739_);
lean_ctor_set(v_reuseFailAlloc_2786_, 2, v_a_2752_);
lean_ctor_set(v_reuseFailAlloc_2786_, 3, v_a_2749_);
lean_ctor_set_uint8(v_reuseFailAlloc_2786_, sizeof(void*)*4, v_safe_2742_);
v___x_2776_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2778_; 
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v_a_2771_);
v___x_2778_ = v___x_2762_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2771_);
v___x_2778_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2780_; 
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 1, v___x_2778_);
lean_ctor_set(v___x_2736_, 0, v___x_2776_);
v___x_2780_ = v___x_2736_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2784_, 2, v_inlineAttr_x3f_2734_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, sizeof(void*)*3, v_recursive_2733_);
v___x_2780_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2782_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 0, v___x_2780_);
v___x_2782_ = v___x_2773_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2780_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_del_object(v___x_2762_);
lean_dec(v_a_2752_);
lean_dec(v_a_2749_);
lean_del_object(v___x_2744_);
lean_dec(v_levelParams_2739_);
lean_dec(v_name_2738_);
lean_del_object(v___x_2736_);
lean_dec(v_inlineAttr_x3f_2734_);
v_a_2788_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2770_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2770_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
}
else
{
lean_object* v_externAttrData_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2847_; 
v_externAttrData_2811_ = lean_ctor_get(v_value_2732_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_value_2732_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2813_ = v_value_2732_;
v_isShared_2814_ = v_isSharedCheck_2847_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_externAttrData_2811_);
lean_dec(v_value_2732_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2847_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v_resultType_2816_; 
if (v___x_2759_ == 0)
{
v_resultType_2816_ = v_a_2752_;
goto v___jp_2815_;
}
else
{
uint8_t v___x_2829_; 
v___x_2829_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_2752_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; 
lean_dec(v_a_2752_);
v___x_2830_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
v_resultType_2816_ = v___x_2830_;
goto v___jp_2815_;
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_del_object(v___x_2813_);
lean_dec(v_externAttrData_2811_);
lean_del_object(v___x_2754_);
lean_dec(v_a_2749_);
lean_del_object(v___x_2744_);
lean_dec(v_levelParams_2739_);
lean_del_object(v___x_2736_);
lean_dec(v_inlineAttr_x3f_2734_);
v___x_2831_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5);
v___x_2832_ = l_Lean_MessageData_ofName(v_name_2738_);
v___x_2833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2831_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = l_Lean_MessageData_ofExpr(v_a_2752_);
v___x_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2835_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2837_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
v___jp_2815_:
{
lean_object* v___x_2818_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 3, v_a_2749_);
lean_ctor_set(v___x_2744_, 2, v_resultType_2816_);
v___x_2818_ = v___x_2744_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_name_2738_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_levelParams_2739_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_resultType_2816_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_a_2749_);
lean_ctor_set_uint8(v_reuseFailAlloc_2828_, sizeof(void*)*4, v_safe_2742_);
v___x_2818_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2820_; 
if (v_isShared_2814_ == 0)
{
v___x_2820_ = v___x_2813_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_externAttrData_2811_);
v___x_2820_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2822_; 
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 1, v___x_2820_);
lean_ctor_set(v___x_2736_, 0, v___x_2818_);
v___x_2822_ = v___x_2736_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_inlineAttr_x3f_2734_);
lean_ctor_set_uint8(v_reuseFailAlloc_2826_, sizeof(void*)*3, v_recursive_2733_);
v___x_2822_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2824_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2822_);
v___x_2824_ = v___x_2754_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
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
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec(v_a_2749_);
lean_del_object(v___x_2744_);
lean_dec(v_levelParams_2739_);
lean_dec(v_name_2738_);
lean_del_object(v___x_2736_);
lean_dec(v_inlineAttr_x3f_2734_);
lean_dec_ref(v_value_2732_);
v_a_2849_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2751_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2751_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_del_object(v___x_2744_);
lean_dec_ref(v_params_2741_);
lean_dec_ref(v_type_2740_);
lean_dec(v_levelParams_2739_);
lean_dec(v_name_2738_);
lean_del_object(v___x_2736_);
lean_dec(v_inlineAttr_x3f_2734_);
lean_dec_ref(v_value_2732_);
v_a_2857_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2748_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2748_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___boxed(lean_object* v_decl_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(lean_object* v_decl_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc_n(v_a_2883_, 2);
lean_dec_ref_known(v___x_2882_, 1);
v___x_2884_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_2883_, v_a_2880_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2891_ == 0)
{
lean_object* v_unused_2892_; 
v_unused_2892_ = lean_ctor_get(v___x_2884_, 0);
lean_dec(v_unused_2892_);
v___x_2886_ = v___x_2884_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_dec(v___x_2884_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v_a_2883_);
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2883_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec(v_a_2883_);
v_a_2893_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2884_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2884_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
return v___x_2882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go___boxed(lean_object* v_decl_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
return v_res_2908_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0(void){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2909_ = lean_box(0);
v___x_2910_ = lean_unsigned_to_nat(16u);
v___x_2911_ = lean_mk_array(v___x_2910_, v___x_2909_);
return v___x_2911_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0);
v___x_2913_ = lean_unsigned_to_nat(0u);
v___x_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
lean_ctor_set(v___x_2914_, 1, v___x_2912_);
return v___x_2914_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2(void){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1);
v___x_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(lean_object* v_decl_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2);
v___x_2924_ = lean_st_mk_ref(v___x_2923_);
v___x_2925_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_2917_, v___x_2924_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2934_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2928_ = v___x_2925_;
v_isShared_2929_ = v_isSharedCheck_2934_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2925_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2934_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2930_ = lean_st_ref_get(v___x_2924_);
lean_dec(v___x_2924_);
lean_dec(v___x_2930_);
if (v_isShared_2929_ == 0)
{
v___x_2932_ = v___x_2928_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2926_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
else
{
lean_dec(v___x_2924_);
return v___x_2925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___boxed(lean_object* v_decl_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_decl_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(size_t v_sz_2942_, size_t v_i_2943_, lean_object* v_bs_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
uint8_t v___x_2950_; 
v___x_2950_ = lean_usize_dec_lt(v_i_2943_, v_sz_2942_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; 
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v_bs_2944_);
return v___x_2951_;
}
else
{
lean_object* v_v_2952_; lean_object* v___x_2953_; 
v_v_2952_ = lean_array_uget_borrowed(v_bs_2944_, v_i_2943_);
lean_inc(v_v_2952_);
v___x_2953_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_v_2952_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; lean_object* v_bs_x27_2956_; size_t v___x_2957_; size_t v___x_2958_; lean_object* v___x_2959_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2955_ = lean_unsigned_to_nat(0u);
v_bs_x27_2956_ = lean_array_uset(v_bs_2944_, v_i_2943_, v___x_2955_);
v___x_2957_ = ((size_t)1ULL);
v___x_2958_ = lean_usize_add(v_i_2943_, v___x_2957_);
v___x_2959_ = lean_array_uset(v_bs_x27_2956_, v_i_2943_, v_a_2954_);
v_i_2943_ = v___x_2958_;
v_bs_2944_ = v___x_2959_;
goto _start;
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec_ref(v_bs_2944_);
v_a_2961_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2953_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2953_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0___boxed(lean_object* v_sz_2969_, lean_object* v_i_2970_, lean_object* v_bs_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
size_t v_sz_boxed_2977_; size_t v_i_boxed_2978_; lean_object* v_res_2979_; 
v_sz_boxed_2977_ = lean_unbox_usize(v_sz_2969_);
lean_dec(v_sz_2969_);
v_i_boxed_2978_ = lean_unbox_usize(v_i_2970_);
lean_dec(v_i_2970_);
v_res_2979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_boxed_2977_, v_i_boxed_2978_, v_bs_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0(lean_object* v_x_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
size_t v_sz_2986_; size_t v___x_2987_; lean_object* v___x_2988_; 
v_sz_2986_ = lean_array_size(v_x_2980_);
v___x_2987_ = ((size_t)0ULL);
v___x_2988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_2986_, v___x_2987_, v_x_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0___boxed(lean_object* v_x_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_Compiler_LCNF_toImpure___lam__0(v_x_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3046_; uint8_t v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3046_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3047_ = 1;
v___x_3048_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3049_ = l_Lean_registerTraceClass(v___x_3046_, v___x_3047_, v___x_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2____boxed(lean_object* v_a_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
return v_res_3051_;
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
