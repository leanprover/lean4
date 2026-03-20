// Lean compiler output
// Module: Lean.Compiler.LCNF.ExplicitBoxing
// Imports: public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.ElimDead import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.LCNF.AuxDeclCache import Lean.Runtime
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_closureMaxArgs;
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object*);
uint8_t l_Lean_Expr_isVoid(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_maxSmallNat;
lean_object* l_Lean_Compiler_LCNF_CtorInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_CtorInfo_isScalar(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updatePapImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "boxed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "res"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 61, 90, 23, 143, 26, 140, 228)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__3_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addBoxedVersions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addBoxedVersions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "_boxed_const"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(112, 157, 119, 166, 190, 88, 106, 4)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__1_value;
static const lean_array_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateLetImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tagged"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 57, 252, 162, 142, 133, 51, 193)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "obj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(240, 235, 44, 74, 242, 121, 239, 90)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__6_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Compiler.LCNF.ExplicitBoxing"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 106, .m_capacity = 106, .m_length = 105, .m_data = "_private.Lean.Compiler.LCNF.ExplicitBoxing.0.Lean.Compiler.LCNF.Code.explicitBoxing.tryCorrectLetDeclType"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "_private.Lean.Compiler.LCNF.ExplicitBoxing.0.Lean.Compiler.LCNF.Code.explicitBoxing.visitLet"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "_private.Lean.Compiler.LCNF.ExplicitBoxing.0.Lean.Compiler.LCNF.Code.explicitBoxing"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_explicitBoxing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBoxing"};
static const lean_object* l_Lean_Compiler_LCNF_explicitBoxing___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_explicitBoxing___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_explicitBoxing___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_explicitBoxing___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 162, 141, 185, 247, 139, 72, 40)}};
static const lean_object* l_Lean_Compiler_LCNF_explicitBoxing___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_explicitBoxing___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_explicitBoxing___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_explicitBoxing___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_explicitBoxing___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_explicitBoxing___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_explicitBoxing___closed__1_value),((lean_object*)&l_Lean_Compiler_LCNF_explicitBoxing___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 2, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_explicitBoxing___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_explicitBoxing___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_explicitBoxing = (const lean_object*)&l_Lean_Compiler_LCNF_explicitBoxing___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_explicitBoxing___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 96, 99, 100, 223, 46, 216, 101)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ExplicitBoxing"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 42, 222, 16, 111, 249, 179, 156)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(108, 8, 207, 169, 143, 212, 226, 30)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 143, 6, 108, 3, 197, 95, 68)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 136, 18, 33, 69, 107, 44, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 225, 110, 155, 173, 102, 72, 215)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(27, 17, 232, 84, 94, 206, 128, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 177, 146, 111, 253, 172, 137, 144)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(71, 38, 219, 234, 30, 215, 82, 129)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 205, 136, 29, 104, 99, 34, 251)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 89, 48, 194, 67, 193, 228, 59)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(184, 138, 155, 10, 111, 76, 192, 98)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)(((size_t)(654907530) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(45, 112, 151, 245, 157, 42, 188, 100)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 83, 245, 87, 79, 251, 66, 10)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 243, 209, 85, 135, 207, 4, 169)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(187, 126, 28, 226, 12, 101, 145, 238)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; lean_object* v_type_6_; uint8_t v_borrow_7_; uint8_t v___x_8_; uint8_t v___y_10_; uint8_t v___x_16_; 
v___x_5_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v_type_6_ = lean_ctor_get(v___x_5_, 2);
v_borrow_7_ = lean_ctor_get_uint8(v___x_5_, sizeof(void*)*3);
v___x_8_ = 1;
v___x_16_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_6_);
if (v___x_16_ == 0)
{
v___y_10_ = v_borrow_7_;
goto v___jp_9_;
}
else
{
v___y_10_ = v___x_16_;
goto v___jp_9_;
}
v___jp_9_:
{
if (v___y_10_ == 0)
{
lean_object* v_type_11_; uint8_t v___x_12_; 
v_type_11_ = lean_ctor_get(v___x_5_, 2);
v___x_12_ = l_Lean_Expr_isVoid(v_type_11_);
if (v___x_12_ == 0)
{
size_t v___x_13_; size_t v___x_14_; 
v___x_13_ = ((size_t)1ULL);
v___x_14_ = lean_usize_add(v_i_2_, v___x_13_);
v_i_2_ = v___x_14_;
goto _start;
}
else
{
return v___x_8_;
}
}
else
{
return v___x_8_;
}
}
}
else
{
uint8_t v___x_17_; 
v___x_17_ = 0;
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0___boxed(lean_object* v_as_18_, lean_object* v_i_19_, lean_object* v_stop_20_){
_start:
{
size_t v_i_boxed_21_; size_t v_stop_boxed_22_; uint8_t v_res_23_; lean_object* v_r_24_; 
v_i_boxed_21_ = lean_unbox_usize(v_i_19_);
lean_dec(v_i_19_);
v_stop_boxed_22_ = lean_unbox_usize(v_stop_20_);
lean_dec(v_stop_20_);
v_res_23_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(v_as_18_, v_i_boxed_21_, v_stop_boxed_22_);
lean_dec_ref(v_as_18_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(lean_object* v_sig_25_, lean_object* v_a_26_){
_start:
{
lean_object* v___x_28_; lean_object* v_name_29_; lean_object* v_type_30_; lean_object* v_params_31_; uint8_t v___y_33_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_28_ = lean_st_ref_get(v_a_26_);
v_name_29_ = lean_ctor_get(v_sig_25_, 0);
lean_inc(v_name_29_);
v_type_30_ = lean_ctor_get(v_sig_25_, 2);
lean_inc_ref(v_type_30_);
v_params_31_ = lean_ctor_get(v_sig_25_, 3);
lean_inc_ref(v_params_31_);
lean_dec_ref(v_sig_25_);
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_array_get_size(v_params_31_);
v___x_43_ = lean_nat_dec_lt(v___x_41_, v___x_42_);
if (v___x_43_ == 0)
{
lean_dec_ref(v_type_30_);
lean_dec(v_name_29_);
lean_dec(v___x_28_);
v___y_33_ = v___x_43_;
goto v___jp_32_;
}
else
{
lean_object* v_env_44_; uint8_t v___y_46_; uint8_t v___x_50_; 
v_env_44_ = lean_ctor_get(v___x_28_, 0);
lean_inc_ref(v_env_44_);
lean_dec(v___x_28_);
v___x_50_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_30_);
lean_dec_ref(v_type_30_);
if (v___x_50_ == 0)
{
if (v___x_43_ == 0)
{
v___y_46_ = v___x_50_;
goto v___jp_45_;
}
else
{
if (v___x_43_ == 0)
{
v___y_46_ = v___x_50_;
goto v___jp_45_;
}
else
{
size_t v___x_51_; size_t v___x_52_; uint8_t v___x_53_; 
v___x_51_ = ((size_t)0ULL);
v___x_52_ = lean_usize_of_nat(v___x_42_);
v___x_53_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(v_params_31_, v___x_51_, v___x_52_);
v___y_46_ = v___x_53_;
goto v___jp_45_;
}
}
}
else
{
v___y_46_ = v___x_50_;
goto v___jp_45_;
}
v___jp_45_:
{
if (v___y_46_ == 0)
{
uint8_t v___x_47_; 
v___x_47_ = l_Lean_isExtern(v_env_44_, v_name_29_);
v___y_33_ = v___x_47_;
goto v___jp_32_;
}
else
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec_ref(v_env_44_);
lean_dec_ref(v_params_31_);
lean_dec(v_name_29_);
v___x_48_ = lean_box(v___y_46_);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
}
v___jp_32_:
{
if (v___y_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_34_ = l_Lean_closureMaxArgs;
v___x_35_ = lean_array_get_size(v_params_31_);
lean_dec_ref(v_params_31_);
v___x_36_ = lean_nat_dec_lt(v___x_34_, v___x_35_);
v___x_37_ = lean_box(v___x_36_);
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
else
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec_ref(v_params_31_);
v___x_39_ = lean_box(v___y_33_);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg___boxed(lean_object* v_sig_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_sig_54_, v_a_55_);
lean_dec(v_a_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion(lean_object* v_sig_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_sig_58_, v_a_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___boxed(lean_object* v_sig_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion(v_sig_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(size_t v_sz_72_, size_t v_i_73_, lean_object* v_bs_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = lean_usize_dec_lt(v_i_73_, v_sz_72_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v_bs_74_);
return v___x_81_;
}
else
{
lean_object* v_v_82_; lean_object* v_binderName_83_; lean_object* v_type_84_; uint8_t v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; 
v_v_82_ = lean_array_uget_borrowed(v_bs_74_, v_i_73_);
v_binderName_83_ = lean_ctor_get(v_v_82_, 1);
v_type_84_ = lean_ctor_get(v_v_82_, 2);
v___x_85_ = 1;
v___x_86_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_84_);
v___x_87_ = 0;
lean_inc(v_binderName_83_);
v___x_88_ = l_Lean_Compiler_LCNF_mkParam(v___x_85_, v_binderName_83_, v___x_86_, v___x_87_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_90_; lean_object* v_bs_x27_91_; size_t v___x_92_; size_t v___x_93_; lean_object* v___x_94_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_a_89_);
lean_dec_ref(v___x_88_);
v___x_90_ = lean_unsigned_to_nat(0u);
v_bs_x27_91_ = lean_array_uset(v_bs_74_, v_i_73_, v___x_90_);
v___x_92_ = ((size_t)1ULL);
v___x_93_ = lean_usize_add(v_i_73_, v___x_92_);
v___x_94_ = lean_array_uset(v_bs_x27_91_, v_i_73_, v_a_89_);
v_i_73_ = v___x_93_;
v_bs_74_ = v___x_94_;
goto _start;
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec_ref(v_bs_74_);
v_a_96_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_88_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_88_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0___boxed(lean_object* v_sz_104_, lean_object* v_i_105_, lean_object* v_bs_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
size_t v_sz_boxed_112_; size_t v_i_boxed_113_; lean_object* v_res_114_; 
v_sz_boxed_112_ = lean_unbox_usize(v_sz_104_);
lean_dec(v_sz_104_);
v_i_boxed_113_ = lean_unbox_usize(v_i_105_);
lean_dec(v_i_105_);
v_res_114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(v_sz_boxed_112_, v_i_boxed_113_, v_bs_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(lean_object* v_as_116_, size_t v_sz_117_, size_t v_i_118_, lean_object* v_b_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_a_126_; uint8_t v___x_130_; 
v___x_130_ = lean_usize_dec_lt(v_i_118_, v_sz_117_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v_b_119_);
return v___x_131_;
}
else
{
lean_object* v_snd_132_; lean_object* v_snd_133_; lean_object* v_fst_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_207_; 
v_snd_132_ = lean_ctor_get(v_b_119_, 1);
lean_inc(v_snd_132_);
v_snd_133_ = lean_ctor_get(v_snd_132_, 1);
lean_inc(v_snd_133_);
v_fst_134_ = lean_ctor_get(v_b_119_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v_b_119_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_b_119_, 1);
lean_dec(v_unused_208_);
v___x_136_ = v_b_119_;
v_isShared_137_ = v_isSharedCheck_207_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_fst_134_);
lean_dec(v_b_119_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_207_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_fst_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_205_; 
v_fst_138_ = lean_ctor_get(v_snd_132_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v_snd_132_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_snd_132_, 1);
lean_dec(v_unused_206_);
v___x_140_ = v_snd_132_;
v_isShared_141_ = v_isSharedCheck_205_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_fst_138_);
lean_dec(v_snd_132_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_205_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v_array_142_; lean_object* v_start_143_; lean_object* v_stop_144_; uint8_t v___x_145_; 
v_array_142_ = lean_ctor_get(v_snd_133_, 0);
v_start_143_ = lean_ctor_get(v_snd_133_, 1);
v_stop_144_ = lean_ctor_get(v_snd_133_, 2);
v___x_145_ = lean_nat_dec_lt(v_start_143_, v_stop_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_147_; 
if (v_isShared_141_ == 0)
{
v___x_147_ = v___x_140_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_fst_138_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_snd_133_);
v___x_147_ = v_reuseFailAlloc_152_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_149_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_147_);
v___x_149_ = v___x_136_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_fst_134_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_151_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; 
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
}
else
{
lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_201_; 
lean_inc(v_stop_144_);
lean_inc(v_start_143_);
lean_inc_ref(v_array_142_);
v_isSharedCheck_201_ = !lean_is_exclusive(v_snd_133_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_202_ = lean_ctor_get(v_snd_133_, 2);
lean_dec(v_unused_202_);
v_unused_203_ = lean_ctor_get(v_snd_133_, 1);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_snd_133_, 0);
lean_dec(v_unused_204_);
v___x_154_ = v_snd_133_;
v_isShared_155_ = v_isSharedCheck_201_;
goto v_resetjp_153_;
}
else
{
lean_dec(v_snd_133_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_201_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v_a_156_; lean_object* v_binderName_157_; lean_object* v_type_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
v_a_156_ = lean_array_uget_borrowed(v_as_116_, v_i_118_);
v_binderName_157_ = lean_ctor_get(v_a_156_, 1);
v_type_158_ = lean_ctor_get(v_a_156_, 2);
v___x_159_ = lean_array_fget(v_array_142_, v_start_143_);
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_nat_add(v_start_143_, v___x_160_);
lean_dec(v_start_143_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v___x_161_);
v___x_163_ = v___x_154_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_array_142_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_stop_144_);
v___x_163_ = v_reuseFailAlloc_200_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
uint8_t v___x_164_; 
v___x_164_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_158_);
if (v___x_164_ == 0)
{
lean_object* v_fvarId_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v_fvarId_165_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_fvarId_165_);
lean_dec(v___x_159_);
v___x_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_166_, 0, v_fvarId_165_);
v___x_167_ = lean_array_push(v_fst_138_, v___x_166_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_163_);
lean_ctor_set(v___x_140_, 0, v___x_167_);
v___x_169_ = v___x_140_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_163_);
v___x_169_ = v_reuseFailAlloc_173_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_171_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_169_);
v___x_171_ = v___x_136_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_fst_134_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
v_a_126_ = v___x_171_;
goto v___jp_125_;
}
}
}
else
{
lean_object* v_fvarId_174_; uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_fvarId_174_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_fvarId_174_);
lean_dec(v___x_159_);
v___x_175_ = 1;
v___x_176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0));
lean_inc(v_binderName_157_);
v___x_177_ = l_Lean_Name_str___override(v_binderName_157_, v___x_176_);
v___x_178_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_178_, 0, v_fvarId_174_);
lean_inc_ref(v_type_158_);
v___x_179_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_175_, v___x_177_, v_type_158_, v___x_178_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v_fvarId_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref(v___x_179_);
v_fvarId_181_ = lean_ctor_get(v_a_180_, 0);
lean_inc(v_fvarId_181_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v_a_180_);
v___x_183_ = lean_array_push(v_fst_134_, v___x_182_);
v___x_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_184_, 0, v_fvarId_181_);
v___x_185_ = lean_array_push(v_fst_138_, v___x_184_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_163_);
lean_ctor_set(v___x_140_, 0, v___x_185_);
v___x_187_ = v___x_140_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v___x_163_);
v___x_187_ = v_reuseFailAlloc_191_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_189_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_187_);
lean_ctor_set(v___x_136_, 0, v___x_183_);
v___x_189_ = v___x_136_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
v_a_126_ = v___x_189_;
goto v___jp_125_;
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec_ref(v___x_163_);
lean_del_object(v___x_140_);
lean_dec(v_fst_138_);
lean_del_object(v___x_136_);
lean_dec(v_fst_134_);
v_a_192_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_179_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_179_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
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
v___jp_125_:
{
size_t v___x_127_; size_t v___x_128_; 
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_add(v_i_118_, v___x_127_);
v_i_118_ = v___x_128_;
v_b_119_ = v_a_126_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___boxed(lean_object* v_as_209_, lean_object* v_sz_210_, lean_object* v_i_211_, lean_object* v_b_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
size_t v_sz_boxed_218_; size_t v_i_boxed_219_; lean_object* v_res_220_; 
v_sz_boxed_218_ = lean_unbox_usize(v_sz_210_);
lean_dec(v_sz_210_);
v_i_boxed_219_ = lean_unbox_usize(v_i_211_);
lean_dec(v_i_211_);
v_res_220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(v_as_209_, v_sz_boxed_218_, v_i_boxed_219_, v_b_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec_ref(v_as_209_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(lean_object* v_sig_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_name_235_; lean_object* v_type_236_; lean_object* v_params_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_356_; 
v_name_235_ = lean_ctor_get(v_sig_229_, 0);
v_type_236_ = lean_ctor_get(v_sig_229_, 2);
v_params_237_ = lean_ctor_get(v_sig_229_, 3);
v_isSharedCheck_356_ = !lean_is_exclusive(v_sig_229_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; 
v_unused_357_ = lean_ctor_get(v_sig_229_, 1);
lean_dec(v_unused_357_);
v___x_239_ = v_sig_229_;
v_isShared_240_ = v_isSharedCheck_356_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_params_237_);
lean_inc(v_type_236_);
lean_inc(v_name_235_);
lean_dec(v_sig_229_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_356_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
size_t v_sz_241_; size_t v___x_242_; lean_object* v___x_243_; 
v_sz_241_ = lean_array_size(v_params_237_);
v___x_242_ = ((size_t)0ULL);
lean_inc_ref(v_params_237_);
v___x_243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(v_sz_241_, v___x_242_, v_params_237_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v_value_246_; lean_object* v___y_247_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_a_244_);
lean_dec_ref(v___x_243_);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0));
v___x_278_ = lean_array_get_size(v_params_237_);
v___x_279_ = lean_mk_empty_array_with_capacity(v___x_278_);
v___x_280_ = lean_array_get_size(v_a_244_);
lean_inc(v_a_244_);
v___x_281_ = l_Array_toSubarray___redArg(v_a_244_, v___x_276_, v___x_280_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_279_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_277_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(v_params_237_, v_sz_241_, v___x_242_, v___x_283_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
lean_dec_ref(v_params_237_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v_snd_286_; lean_object* v_fst_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_339_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref(v___x_284_);
v_snd_286_ = lean_ctor_get(v_a_285_, 1);
v_fst_287_ = lean_ctor_get(v_a_285_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v_a_285_);
if (v_isSharedCheck_339_ == 0)
{
v___x_289_ = v_a_285_;
v_isShared_290_ = v_isSharedCheck_339_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_snd_286_);
lean_inc(v_fst_287_);
lean_dec(v_a_285_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_339_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v_fst_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_337_; 
v_fst_291_ = lean_ctor_get(v_snd_286_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_snd_286_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_snd_286_, 1);
lean_dec(v_unused_338_);
v___x_293_ = v_snd_286_;
v_isShared_294_ = v_isSharedCheck_337_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_fst_291_);
lean_dec(v_snd_286_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_337_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_295_ = 1;
v___x_296_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2));
lean_inc(v_name_235_);
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 9);
lean_ctor_set(v___x_293_, 1, v_fst_291_);
lean_ctor_set(v___x_293_, 0, v_name_235_);
v___x_298_ = v___x_293_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_name_235_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_fst_291_);
v___x_298_ = v_reuseFailAlloc_336_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; 
lean_inc_ref(v_type_236_);
v___x_299_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_295_, v___x_296_, v_type_236_, v___x_298_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref(v___x_299_);
lean_inc(v_a_300_);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v_a_300_);
v___x_302_ = lean_array_push(v_fst_287_, v___x_301_);
v___x_303_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_236_);
if (v___x_303_ == 0)
{
lean_object* v_fvarId_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_del_object(v___x_289_);
v_fvarId_304_ = lean_ctor_get(v_a_300_, 0);
lean_inc(v_fvarId_304_);
lean_dec(v_a_300_);
v___x_305_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_305_, 0, v_fvarId_304_);
v___x_306_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_295_, v___x_302_, v___x_305_);
lean_dec_ref(v___x_302_);
v_value_246_ = v___x_306_;
v___y_247_ = v_a_233_;
goto v___jp_245_;
}
else
{
lean_object* v_fvarId_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v_fvarId_307_ = lean_ctor_get(v_a_300_, 0);
lean_inc(v_fvarId_307_);
lean_dec(v_a_300_);
v___x_308_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4));
v___x_309_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_236_);
lean_inc_ref(v_type_236_);
if (v_isShared_290_ == 0)
{
lean_ctor_set_tag(v___x_289_, 13);
lean_ctor_set(v___x_289_, 1, v_fvarId_307_);
lean_ctor_set(v___x_289_, 0, v_type_236_);
v___x_311_ = v___x_289_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_type_236_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_fvarId_307_);
v___x_311_ = v_reuseFailAlloc_327_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_295_, v___x_308_, v___x_309_, v___x_311_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v_fvarId_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref(v___x_312_);
v_fvarId_314_ = lean_ctor_get(v_a_313_, 0);
lean_inc(v_fvarId_314_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v_a_313_);
v___x_316_ = lean_array_push(v___x_302_, v___x_315_);
v___x_317_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_317_, 0, v_fvarId_314_);
v___x_318_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_295_, v___x_316_, v___x_317_);
lean_dec_ref(v___x_316_);
v_value_246_ = v___x_318_;
v___y_247_ = v_a_233_;
goto v___jp_245_;
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec_ref(v___x_302_);
lean_dec(v_a_244_);
lean_del_object(v___x_239_);
lean_dec_ref(v_type_236_);
lean_dec(v_name_235_);
v_a_319_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_312_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_312_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_del_object(v___x_289_);
lean_dec(v_fst_287_);
lean_dec(v_a_244_);
lean_del_object(v___x_239_);
lean_dec_ref(v_type_236_);
lean_dec(v_name_235_);
v_a_328_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_299_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_299_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_a_244_);
lean_del_object(v___x_239_);
lean_dec_ref(v_type_236_);
lean_dec(v_name_235_);
v_a_340_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_284_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_284_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
v___jp_245_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; lean_object* v___x_253_; 
v___x_248_ = l_Lean_Compiler_LCNF_mkBoxedName(v_name_235_);
v___x_249_ = lean_box(0);
v___x_250_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_236_);
lean_dec_ref(v_type_236_);
v___x_251_ = 1;
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 3, v_a_244_);
lean_ctor_set(v___x_239_, 2, v___x_250_);
lean_ctor_set(v___x_239_, 1, v___x_249_);
lean_ctor_set(v___x_239_, 0, v___x_248_);
v___x_253_ = v___x_239_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_275_, 3, v_a_244_);
v___x_253_ = v_reuseFailAlloc_275_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; uint8_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*4, v___x_251_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v_value_246_);
v___x_255_ = 0;
v___x_256_ = lean_box(0);
v___x_257_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_257_, 0, v___x_253_);
lean_ctor_set(v___x_257_, 1, v___x_254_);
lean_ctor_set(v___x_257_, 2, v___x_256_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*3, v___x_255_);
lean_inc_ref(v___x_257_);
v___x_258_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v___x_257_, v___y_247_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; 
v_unused_266_ = lean_ctor_get(v___x_258_, 0);
lean_dec(v_unused_266_);
v___x_260_ = v___x_258_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_dec(v___x_258_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_257_);
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_257_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec_ref(v___x_257_);
v_a_267_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_258_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_258_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_del_object(v___x_239_);
lean_dec_ref(v_params_237_);
lean_dec_ref(v_type_236_);
lean_dec(v_name_235_);
v_a_348_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_243_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_243_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___boxed(lean_object* v_sig_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(v_sig_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(lean_object* v_as_365_, size_t v_i_366_, size_t v_stop_367_, lean_object* v_b_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_a_375_; uint8_t v___x_379_; 
v___x_379_ = lean_usize_dec_eq(v_i_366_, v_stop_367_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v_toSignature_381_; lean_object* v___x_382_; 
v___x_380_ = lean_array_uget_borrowed(v_as_365_, v_i_366_);
v_toSignature_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc_ref(v_toSignature_381_);
v___x_382_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_toSignature_381_, v___y_372_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; uint8_t v___x_384_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref(v___x_382_);
v___x_384_ = lean_unbox(v_a_383_);
lean_dec(v_a_383_);
if (v___x_384_ == 0)
{
v_a_375_ = v_b_368_;
goto v___jp_374_;
}
else
{
lean_object* v___x_385_; 
lean_inc_ref(v_toSignature_381_);
v___x_385_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(v_toSignature_381_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref(v___x_385_);
v___x_387_ = lean_array_push(v_b_368_, v_a_386_);
v_a_375_ = v___x_387_;
goto v___jp_374_;
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec_ref(v_b_368_);
v_a_388_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_385_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_385_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec_ref(v_b_368_);
v_a_396_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_382_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_382_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
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
else
{
lean_object* v___x_404_; 
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v_b_368_);
return v___x_404_;
}
v___jp_374_:
{
size_t v___x_376_; size_t v___x_377_; 
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_add(v_i_366_, v___x_376_);
v_i_366_ = v___x_377_;
v_b_368_ = v_a_375_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0___boxed(lean_object* v_as_405_, lean_object* v_i_406_, lean_object* v_stop_407_, lean_object* v_b_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
size_t v_i_boxed_414_; size_t v_stop_boxed_415_; lean_object* v_res_416_; 
v_i_boxed_414_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_stop_boxed_415_ = lean_unbox_usize(v_stop_407_);
lean_dec(v_stop_407_);
v_res_416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_405_, v_i_boxed_414_, v_stop_boxed_415_, v_b_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec_ref(v_as_405_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(lean_object* v_as_419_, lean_object* v_start_420_, lean_object* v_stop_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0));
v___x_428_ = lean_nat_dec_lt(v_start_420_, v_stop_421_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_array_get_size(v_as_419_);
v___x_431_ = lean_nat_dec_le(v_stop_421_, v___x_430_);
if (v___x_431_ == 0)
{
uint8_t v___x_432_; 
v___x_432_ = lean_nat_dec_lt(v_start_420_, v___x_430_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_427_);
return v___x_433_;
}
else
{
size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_usize_of_nat(v_start_420_);
v___x_435_ = lean_usize_of_nat(v___x_430_);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_419_, v___x_434_, v___x_435_, v___x_427_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
return v___x_436_;
}
}
else
{
size_t v___x_437_; size_t v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_usize_of_nat(v_start_420_);
v___x_438_ = lean_usize_of_nat(v_stop_421_);
v___x_439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_419_, v___x_437_, v___x_438_, v___x_427_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
return v___x_439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___boxed(lean_object* v_as_440_, lean_object* v_start_441_, lean_object* v_stop_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(v_as_440_, v_start_441_, v_stop_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v_stop_442_);
lean_dec(v_start_441_);
lean_dec_ref(v_as_440_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addBoxedVersions(lean_object* v_decls_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_array_get_size(v_decls_449_);
v___x_457_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(v_decls_449_, v___x_455_, v___x_456_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_466_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_466_ == 0)
{
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = l_Array_append___redArg(v_decls_449_, v_a_458_);
lean_dec(v_a_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_462_);
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
else
{
lean_dec_ref(v_decls_449_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addBoxedVersions___boxed(lean_object* v_decls_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Compiler_LCNF_addBoxedVersions(v_decls_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(lean_object* v_a_474_){
_start:
{
lean_object* v_currDeclResultType_476_; lean_object* v___x_477_; 
v_currDeclResultType_476_ = lean_ctor_get(v_a_474_, 1);
lean_inc_ref(v_currDeclResultType_476_);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v_currDeclResultType_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg___boxed(lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(v_a_478_);
lean_dec_ref(v_a_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_currDeclResultType_488_; lean_object* v___x_489_; 
v_currDeclResultType_488_ = lean_ctor_get(v_a_481_, 1);
lean_inc_ref(v_currDeclResultType_488_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v_currDeclResultType_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___boxed(lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
return v_res_497_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(lean_object* v_t_u2081_498_, lean_object* v_t_u2082_499_){
_start:
{
uint8_t v___y_501_; uint8_t v___y_505_; uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2081_498_);
v___x_507_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2082_499_);
if (v___x_506_ == 0)
{
if (v___x_507_ == 0)
{
uint8_t v___x_508_; 
v___x_508_ = 1;
v___y_501_ = v___x_508_;
goto v___jp_500_;
}
else
{
v___y_505_ = v___x_506_;
goto v___jp_504_;
}
}
else
{
v___y_505_ = v___x_507_;
goto v___jp_504_;
}
v___jp_500_:
{
uint8_t v___x_502_; 
v___x_502_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2081_498_);
if (v___x_502_ == 0)
{
return v___y_501_;
}
else
{
uint8_t v___x_503_; 
v___x_503_ = lean_expr_eqv(v_t_u2081_498_, v_t_u2082_499_);
return v___x_503_;
}
}
v___jp_504_:
{
if (v___y_505_ == 0)
{
return v___y_505_;
}
else
{
v___y_501_ = v___y_505_;
goto v___jp_500_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing___boxed(lean_object* v_t_u2081_509_, lean_object* v_t_u2082_510_){
_start:
{
uint8_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_t_u2081_509_, v_t_u2082_510_);
lean_dec_ref(v_t_u2082_510_);
lean_dec_ref(v_t_u2081_509_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(lean_object* v_x_515_, lean_object* v_xType_516_, lean_object* v_a_517_){
_start:
{
lean_object* v___y_520_; 
if (lean_obj_tag(v_xType_516_) == 4)
{
lean_object* v_declName_559_; 
v_declName_559_ = lean_ctor_get(v_xType_516_, 0);
if (lean_obj_tag(v_declName_559_) == 1)
{
lean_object* v_pre_560_; 
v_pre_560_ = lean_ctor_get(v_declName_559_, 0);
if (lean_obj_tag(v_pre_560_) == 0)
{
lean_object* v_us_561_; lean_object* v_str_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_us_561_ = lean_ctor_get(v_xType_516_, 1);
v_str_562_ = lean_ctor_get(v_declName_559_, 1);
v___x_563_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0));
v___x_564_ = lean_string_dec_eq(v_str_562_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1));
v___x_566_ = lean_string_dec_eq(v_str_562_, v___x_565_);
if (v___x_566_ == 0)
{
v___y_520_ = v_a_517_;
goto v___jp_519_;
}
else
{
if (lean_obj_tag(v_us_561_) == 0)
{
goto v___jp_556_;
}
else
{
v___y_520_ = v_a_517_;
goto v___jp_519_;
}
}
}
else
{
if (lean_obj_tag(v_us_561_) == 0)
{
goto v___jp_556_;
}
else
{
v___y_520_ = v_a_517_;
goto v___jp_519_;
}
}
}
else
{
v___y_520_ = v_a_517_;
goto v___jp_519_;
}
}
else
{
v___y_520_ = v_a_517_;
goto v___jp_519_;
}
}
else
{
v___y_520_ = v_a_517_;
goto v___jp_519_;
}
v___jp_519_:
{
uint8_t v___x_521_; lean_object* v___x_522_; 
v___x_521_ = 1;
v___x_522_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_521_, v_x_515_, v___y_520_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
if (lean_obj_tag(v_a_523_) == 1)
{
lean_object* v_val_524_; 
v_val_524_ = lean_ctor_get(v_a_523_, 0);
lean_inc(v_val_524_);
lean_dec_ref(v_a_523_);
switch(lean_obj_tag(v_val_524_))
{
case 0:
{
lean_dec_ref(v_val_524_);
return v___x_522_;
}
case 9:
{
lean_object* v_args_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_args_525_ = lean_ctor_get(v_val_524_, 1);
lean_inc_ref(v_args_525_);
lean_dec_ref(v_val_524_);
v___x_526_ = lean_array_get_size(v_args_525_);
lean_dec_ref(v_args_525_);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_nat_dec_eq(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v___x_522_, 0);
lean_dec(v_unused_537_);
v___x_530_ = v___x_522_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_dec(v___x_522_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_box(0);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
return v___x_522_;
}
}
default: 
{
lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_545_; 
lean_dec(v_val_524_);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; 
v_unused_546_ = lean_ctor_get(v___x_522_, 0);
lean_dec(v_unused_546_);
v___x_539_ = v___x_522_;
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
else
{
lean_dec(v___x_522_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_box(0);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
else
{
lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_a_523_);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v___x_522_, 0);
lean_dec(v_unused_555_);
v___x_548_ = v___x_522_;
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
else
{
lean_dec(v___x_522_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_box(0);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_550_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
return v___x_522_;
}
}
v___jp_556_:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_box(0);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___boxed(lean_object* v_x_567_, lean_object* v_xType_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_x_567_, v_xType_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_xType_568_);
lean_dec(v_x_567_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(lean_object* v_x_572_, lean_object* v_xType_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_x_572_, v_xType_573_, v_a_577_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___boxed(lean_object* v_x_582_, lean_object* v_xType_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(v_x_582_, v_xType_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec_ref(v_xType_583_);
lean_dec(v_x_582_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(lean_object* v_fvarId_597_, lean_object* v_fvarIdType_598_, lean_object* v_expectedType_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
uint8_t v___x_607_; 
v___x_607_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_expectedType_599_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
v___x_608_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_fvarId_597_, v_fvarIdType_598_, v_a_603_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_740_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_740_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_740_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_740_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
if (lean_obj_tag(v_a_609_) == 0)
{
lean_object* v___x_613_; lean_object* v___x_615_; 
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_expectedType_599_);
v___x_613_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_613_, 0, v_fvarIdType_598_);
lean_ctor_set(v___x_613_, 1, v_fvarId_597_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
else
{
lean_object* v_val_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_739_; 
lean_del_object(v___x_611_);
lean_dec(v_fvarId_597_);
v_val_617_ = lean_ctor_get(v_a_609_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_a_609_);
if (v_isSharedCheck_739_ == 0)
{
v___x_619_ = v_a_609_;
v_isShared_620_ = v_isSharedCheck_739_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_val_617_);
lean_dec(v_a_609_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_739_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = 1;
v___x_622_ = lean_box(0);
lean_inc_ref(v_fvarIdType_598_);
v___x_623_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_621_, v___x_622_, v_fvarIdType_598_, v_val_617_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v_fvarId_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref(v___x_623_);
v_fvarId_625_ = lean_ctor_get(v_a_624_, 0);
lean_inc(v_fvarId_625_);
v___x_626_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_626_, 0, v_fvarIdType_598_);
lean_ctor_set(v___x_626_, 1, v_fvarId_625_);
lean_inc_ref(v_expectedType_599_);
v___x_627_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_621_, v___x_622_, v_expectedType_599_, v___x_626_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v_fvarId_629_; lean_object* v___x_630_; lean_object* v_currDecl_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_721_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref(v___x_627_);
v_fvarId_629_ = lean_ctor_get(v_a_628_, 0);
v___x_630_ = lean_st_ref_get(v_a_601_);
v_currDecl_631_ = lean_ctor_get(v_a_600_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v_a_600_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v_a_600_, 1);
lean_dec(v_unused_722_);
v___x_633_ = v_a_600_;
v_isShared_634_ = v_isSharedCheck_721_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_currDecl_631_);
lean_dec(v_a_600_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_721_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v_nextAuxIdx_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_719_; 
v_nextAuxIdx_635_ = lean_ctor_get(v___x_630_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v___x_630_, 0);
lean_dec(v_unused_720_);
v___x_637_ = v___x_630_;
v_isShared_638_ = v_isSharedCheck_719_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_nextAuxIdx_635_);
lean_dec(v___x_630_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_719_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
lean_inc(v_fvarId_629_);
if (v_isShared_620_ == 0)
{
lean_ctor_set_tag(v___x_619_, 5);
lean_ctor_set(v___x_619_, 0, v_fvarId_629_);
v___x_640_ = v___x_619_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_fvarId_629_);
v___x_640_ = v_reuseFailAlloc_718_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v___x_640_);
lean_ctor_set(v___x_637_, 0, v_a_628_);
v___x_642_ = v___x_637_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_628_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_640_);
v___x_642_ = v_reuseFailAlloc_717_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
uint8_t v___x_643_; lean_object* v___x_645_; 
v___x_643_ = 1;
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_642_);
lean_ctor_set(v___x_633_, 0, v_a_624_);
v___x_645_ = v___x_633_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_624_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v___x_642_);
v___x_645_ = v_reuseFailAlloc_716_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_646_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__1));
v___x_647_ = lean_name_append_index_after(v___x_646_, v_nextAuxIdx_635_);
v___x_648_ = l_Lean_Name_append(v_currDecl_631_, v___x_647_);
v___x_649_ = lean_box(0);
v___x_650_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__2));
lean_inc(v___x_648_);
v___x_651_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_651_, 0, v___x_648_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
lean_ctor_set(v___x_651_, 2, v_expectedType_599_);
lean_ctor_set(v___x_651_, 3, v___x_650_);
lean_ctor_set_uint8(v___x_651_, sizeof(void*)*4, v___x_643_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_645_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_654_, 0, v___x_651_);
lean_ctor_set(v___x_654_, 1, v___x_652_);
lean_ctor_set(v___x_654_, 2, v___x_653_);
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*3, v___x_607_);
lean_inc(v_a_605_);
lean_inc_ref(v_a_604_);
lean_inc_ref(v___x_654_);
v___x_655_ = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(v___x_621_, v___x_654_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref(v___x_655_);
if (lean_obj_tag(v_a_656_) == 0)
{
lean_object* v___x_657_; lean_object* v_auxDecls_658_; lean_object* v_nextAuxIdx_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
v___x_657_ = lean_st_ref_take(v_a_601_);
v_auxDecls_658_ = lean_ctor_get(v___x_657_, 0);
v_nextAuxIdx_659_ = lean_ctor_get(v___x_657_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_688_ == 0)
{
v___x_661_ = v___x_657_;
v_isShared_662_ = v_isSharedCheck_688_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_nextAuxIdx_659_);
lean_inc(v_auxDecls_658_);
lean_dec(v___x_657_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_688_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
lean_inc_ref(v___x_654_);
v___x_663_ = lean_array_push(v_auxDecls_658_, v___x_654_);
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = lean_nat_add(v_nextAuxIdx_659_, v___x_664_);
lean_dec(v_nextAuxIdx_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___x_665_);
lean_ctor_set(v___x_661_, 0, v___x_663_);
v___x_667_ = v___x_661_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_687_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_st_ref_set(v_a_601_, v___x_667_);
v___x_669_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v___x_654_, v_a_605_);
lean_dec(v_a_605_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v___x_669_, 0);
lean_dec(v_unused_678_);
v___x_671_ = v___x_669_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_dec(v___x_669_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_648_);
lean_ctor_set(v___x_673_, 1, v___x_650_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec(v___x_648_);
v_a_679_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_669_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_669_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
}
else
{
lean_object* v_declName_689_; lean_object* v___x_690_; 
lean_dec(v___x_648_);
v_declName_689_ = lean_ctor_get(v_a_656_, 0);
lean_inc(v_declName_689_);
lean_dec_ref(v_a_656_);
v___x_690_ = l_Lean_Compiler_LCNF_eraseDecl(v___x_621_, v___x_654_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_698_; 
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; 
v_unused_699_ = lean_ctor_get(v___x_690_, 0);
lean_dec(v_unused_699_);
v___x_692_ = v___x_690_;
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
else
{
lean_dec(v___x_690_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_694_, 0, v_declName_689_);
lean_ctor_set(v___x_694_, 1, v___x_650_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec(v_declName_689_);
v_a_700_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_690_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_690_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v___x_654_);
lean_dec(v___x_648_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
v_a_708_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_655_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_655_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
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
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_a_624_);
lean_del_object(v___x_619_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_expectedType_599_);
v_a_723_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_627_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_627_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_del_object(v___x_619_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_expectedType_599_);
lean_dec_ref(v_fvarIdType_598_);
v_a_731_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_623_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_623_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_expectedType_599_);
lean_dec_ref(v_fvarIdType_598_);
lean_dec(v_fvarId_597_);
v_a_741_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_608_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_608_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; 
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_expectedType_599_);
lean_dec_ref(v_fvarIdType_598_);
v___x_749_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_749_, 0, v_fvarId_597_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___boxed(lean_object* v_fvarId_751_, lean_object* v_fvarIdType_752_, lean_object* v_expectedType_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_751_, v_fvarIdType_752_, v_expectedType_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
lean_dec(v_a_755_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(lean_object* v_fvarId_762_, lean_object* v_expectedType_763_, lean_object* v_k_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___x_772_; 
lean_inc(v_fvarId_762_);
v___x_772_ = l_Lean_Compiler_LCNF_getType(v_fvarId_762_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; uint8_t v___x_774_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_772_);
v___x_774_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_773_, v_expectedType_763_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_inc(v_a_770_);
lean_inc_ref(v_a_769_);
lean_inc(v_a_768_);
lean_inc_ref(v_a_767_);
lean_inc_ref(v_a_765_);
lean_inc_ref(v_expectedType_763_);
v___x_775_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_762_, v_a_773_, v_expectedType_763_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v___x_775_);
v___x_777_ = 1;
v___x_778_ = lean_box(0);
v___x_779_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_777_, v___x_778_, v_expectedType_763_, v_a_776_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v_fvarId_781_; lean_object* v___x_782_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref(v___x_779_);
v_fvarId_781_ = lean_ctor_get(v_a_780_, 0);
lean_inc(v_fvarId_781_);
v___x_782_ = lean_apply_8(v_k_764_, v_fvarId_781_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, lean_box(0));
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_791_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_791_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_791_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_791_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_a_780_);
lean_ctor_set(v___x_787_, 1, v_a_783_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_787_);
v___x_789_ = v___x_785_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_dec(v_a_780_);
return v___x_782_;
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec_ref(v_k_764_);
v_a_792_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_779_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_779_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec_ref(v_k_764_);
lean_dec_ref(v_expectedType_763_);
v_a_800_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_775_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_775_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
else
{
lean_object* v___x_808_; 
lean_dec(v_a_773_);
lean_dec_ref(v_expectedType_763_);
v___x_808_ = lean_apply_8(v_k_764_, v_fvarId_762_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, lean_box(0));
return v___x_808_;
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec_ref(v_k_764_);
lean_dec_ref(v_expectedType_763_);
lean_dec(v_fvarId_762_);
v_a_809_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_772_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_772_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded___boxed(lean_object* v_fvarId_817_, lean_object* v_expectedType_818_, lean_object* v_k_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(v_fvarId_817_, v_expectedType_818_, v_k_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(lean_object* v_arg_828_, lean_object* v_k_829_, lean_object* v_x_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(v_arg_828_, v_x_830_);
v___x_839_ = lean_apply_8(v_k_829_, v___x_838_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, lean_box(0));
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0___boxed(lean_object* v_arg_840_, lean_object* v_k_841_, lean_object* v_x_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_840_, v_k_841_, v_x_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(lean_object* v_arg_851_, lean_object* v_expectedType_852_, lean_object* v_k_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
if (lean_obj_tag(v_arg_851_) == 0)
{
lean_object* v___x_861_; 
lean_dec_ref(v_expectedType_852_);
v___x_861_ = lean_apply_8(v_k_853_, v_arg_851_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, lean_box(0));
return v___x_861_;
}
else
{
lean_object* v_fvarId_862_; lean_object* v___x_863_; 
v_fvarId_862_ = lean_ctor_get(v_arg_851_, 0);
lean_inc(v_fvarId_862_);
v___x_863_ = l_Lean_Compiler_LCNF_getType(v_fvarId_862_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; uint8_t v___x_865_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref(v___x_863_);
v___x_865_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_864_, v_expectedType_852_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; 
lean_inc(v_a_859_);
lean_inc_ref(v_a_858_);
lean_inc(v_a_857_);
lean_inc_ref(v_a_856_);
lean_inc_ref(v_a_854_);
lean_inc_ref(v_expectedType_852_);
lean_inc(v_fvarId_862_);
v___x_866_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_862_, v_a_864_, v_expectedType_852_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref(v___x_866_);
v___x_868_ = 1;
v___x_869_ = lean_box(0);
v___x_870_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_868_, v___x_869_, v_expectedType_852_, v_a_867_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v_fvarId_872_; lean_object* v___x_873_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref(v___x_870_);
v_fvarId_872_ = lean_ctor_get(v_a_871_, 0);
lean_inc(v_fvarId_872_);
v___x_873_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_851_, v_k_853_, v_fvarId_872_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_882_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_882_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_882_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_882_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v_a_871_);
lean_ctor_set(v___x_878_, 1, v_a_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_878_);
v___x_880_ = v___x_876_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
else
{
lean_dec(v_a_871_);
return v___x_873_;
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec_ref(v_arg_851_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec_ref(v_k_853_);
v_a_883_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_870_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_870_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v_arg_851_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_expectedType_852_);
v_a_891_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_866_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_866_);
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
else
{
lean_object* v___x_899_; 
lean_inc(v_fvarId_862_);
lean_dec(v_a_864_);
lean_dec_ref(v_expectedType_852_);
v___x_899_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_851_, v_k_853_, v_fvarId_862_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
return v___x_899_;
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec_ref(v_arg_851_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_expectedType_852_);
v_a_900_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_863_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_863_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___boxed(lean_object* v_arg_908_, lean_object* v_expectedType_909_, lean_object* v_k_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(v_arg_908_, v_expectedType_909_, v_k_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(lean_object* v_upperBound_919_, lean_object* v_args_920_, lean_object* v_typeFromIdx_921_, lean_object* v_a_922_, lean_object* v_b_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_a_932_; uint8_t v___x_936_; 
v___x_936_ = lean_nat_dec_lt(v_a_922_, v_upperBound_919_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_924_);
lean_dec(v_a_922_);
lean_dec_ref(v_typeFromIdx_921_);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v_b_923_);
return v___x_937_;
}
else
{
lean_object* v_fst_938_; lean_object* v_snd_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_1002_; 
v_fst_938_ = lean_ctor_get(v_b_923_, 0);
v_snd_939_ = lean_ctor_get(v_b_923_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_b_923_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_941_ = v_b_923_;
v_isShared_942_ = v_isSharedCheck_1002_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_snd_939_);
lean_inc(v_fst_938_);
lean_dec(v_b_923_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_1002_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; 
v___x_943_ = lean_array_fget(v_args_920_, v_a_922_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_944_ = lean_array_push(v_fst_938_, v___x_943_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_snd_939_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
v_a_932_ = v___x_946_;
goto v___jp_931_;
}
}
else
{
lean_object* v_fvarId_948_; lean_object* v___x_949_; 
v_fvarId_948_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_fvarId_948_);
v___x_949_ = l_Lean_Compiler_LCNF_getType(v_fvarId_948_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref(v___x_949_);
lean_inc_ref(v_typeFromIdx_921_);
lean_inc(v_a_922_);
v___x_951_ = lean_apply_1(v_typeFromIdx_921_, v_a_922_);
v___x_952_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_950_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_988_; 
lean_inc(v_fvarId_948_);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v___x_943_, 0);
lean_dec(v_unused_989_);
v___x_954_ = v___x_943_;
v_isShared_955_ = v_isSharedCheck_988_;
goto v_resetjp_953_;
}
else
{
lean_dec(v___x_943_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_988_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; 
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc_ref(v___y_924_);
lean_inc_ref(v___x_951_);
v___x_956_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_948_, v_a_950_, v___x_951_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; uint8_t v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref(v___x_956_);
v___x_958_ = 1;
v___x_959_ = lean_box(0);
v___x_960_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_958_, v___x_959_, v___x_951_, v_a_957_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v_fvarId_962_; lean_object* v___x_964_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref(v___x_960_);
v_fvarId_962_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_fvarId_962_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v_fvarId_962_);
v___x_964_ = v___x_954_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_fvarId_962_);
v___x_964_ = v_reuseFailAlloc_971_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_965_ = lean_array_push(v_fst_938_, v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v_a_961_);
v___x_967_ = lean_array_push(v_snd_939_, v___x_966_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v___x_967_);
lean_ctor_set(v___x_941_, 0, v___x_965_);
v___x_969_ = v___x_941_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
v_a_932_ = v___x_969_;
goto v___jp_931_;
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_del_object(v___x_954_);
lean_del_object(v___x_941_);
lean_dec(v_snd_939_);
lean_dec(v_fst_938_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_924_);
lean_dec(v_a_922_);
lean_dec_ref(v_typeFromIdx_921_);
v_a_972_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_960_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_960_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_del_object(v___x_954_);
lean_dec_ref(v___x_951_);
lean_del_object(v___x_941_);
lean_dec(v_snd_939_);
lean_dec(v_fst_938_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_924_);
lean_dec(v_a_922_);
lean_dec_ref(v_typeFromIdx_921_);
v_a_980_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_956_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_956_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_992_; 
lean_dec_ref(v___x_951_);
lean_dec(v_a_950_);
v___x_990_ = lean_array_push(v_fst_938_, v___x_943_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_990_);
v___x_992_ = v___x_941_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_snd_939_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
v_a_932_ = v___x_992_;
goto v___jp_931_;
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec_ref(v___x_943_);
lean_del_object(v___x_941_);
lean_dec(v_snd_939_);
lean_dec(v_fst_938_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_924_);
lean_dec(v_a_922_);
lean_dec_ref(v_typeFromIdx_921_);
v_a_994_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_949_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_949_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
v___jp_931_:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_unsigned_to_nat(1u);
v___x_934_ = lean_nat_add(v_a_922_, v___x_933_);
lean_dec(v_a_922_);
v_a_922_ = v___x_934_;
v_b_923_ = v_a_932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg___boxed(lean_object* v_upperBound_1003_, lean_object* v_args_1004_, lean_object* v_typeFromIdx_1005_, lean_object* v_a_1006_, lean_object* v_b_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v_upperBound_1003_, v_args_1004_, v_typeFromIdx_1005_, v_a_1006_, v_b_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1009_);
lean_dec_ref(v_args_1004_);
lean_dec(v_upperBound_1003_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(lean_object* v_args_1016_, lean_object* v_typeFromIdx_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; lean_object* v_newArgs_1026_; lean_object* v___x_1027_; lean_object* v_casters_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1025_ = lean_array_get_size(v_args_1016_);
v_newArgs_1026_ = lean_mk_empty_array_with_capacity(v___x_1025_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v_casters_1028_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0));
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_newArgs_1026_);
lean_ctor_set(v___x_1029_, 1, v_casters_1028_);
v___x_1030_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v___x_1025_, v_args_1016_, v_typeFromIdx_1017_, v___x_1027_, v___x_1029_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1047_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1047_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1047_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_fst_1035_; lean_object* v_snd_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1046_; 
v_fst_1035_ = lean_ctor_get(v_a_1031_, 0);
v_snd_1036_ = lean_ctor_get(v_a_1031_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_a_1031_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1038_ = v_a_1031_;
v_isShared_1039_ = v_isSharedCheck_1046_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_snd_1036_);
lean_inc(v_fst_1035_);
lean_dec(v_a_1031_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1046_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_fst_1035_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_snd_1036_);
v___x_1041_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1043_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1041_);
v___x_1043_ = v___x_1033_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
else
{
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux___boxed(lean_object* v_args_1048_, lean_object* v_typeFromIdx_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1048_, v_typeFromIdx_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1051_);
lean_dec_ref(v_args_1048_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(lean_object* v_upperBound_1058_, lean_object* v_args_1059_, lean_object* v_typeFromIdx_1060_, lean_object* v_inst_1061_, lean_object* v_R_1062_, lean_object* v_a_1063_, lean_object* v_b_1064_, lean_object* v_c_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v_upperBound_1058_, v_args_1059_, v_typeFromIdx_1060_, v_a_1063_, v_b_1064_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___boxed(lean_object* v_upperBound_1074_, lean_object* v_args_1075_, lean_object* v_typeFromIdx_1076_, lean_object* v_inst_1077_, lean_object* v_R_1078_, lean_object* v_a_1079_, lean_object* v_b_1080_, lean_object* v_c_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(v_upperBound_1074_, v_args_1075_, v_typeFromIdx_1076_, v_inst_1077_, v_R_1078_, v_a_1079_, v_b_1080_, v_c_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1083_);
lean_dec_ref(v_args_1075_);
lean_dec(v_upperBound_1074_);
return v_res_1089_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0(void){
_start:
{
uint8_t v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = 1;
v___x_1091_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(lean_object* v_ps_1092_, lean_object* v_i_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_type_1096_; 
v___x_1094_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0);
v___x_1095_ = lean_array_get_borrowed(v___x_1094_, v_ps_1092_, v_i_1093_);
v_type_1096_ = lean_ctor_get(v___x_1095_, 2);
lean_inc_ref(v_type_1096_);
return v_type_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed(lean_object* v_ps_1097_, lean_object* v_i_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(v_ps_1097_, v_i_1098_);
lean_dec(v_i_1098_);
lean_dec_ref(v_ps_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(lean_object* v_args_1100_, lean_object* v_ps_1101_, lean_object* v_k_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___f_1110_; lean_object* v___x_1111_; 
v___f_1110_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1110_, 0, v_ps_1101_);
lean_inc(v_a_1108_);
lean_inc_ref(v_a_1107_);
lean_inc(v_a_1106_);
lean_inc_ref(v_a_1105_);
lean_inc_ref(v_a_1103_);
v___x_1111_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1100_, v___f_1110_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v_fst_1113_; lean_object* v_snd_1114_; lean_object* v___x_1115_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref(v___x_1111_);
v_fst_1113_ = lean_ctor_get(v_a_1112_, 0);
lean_inc(v_fst_1113_);
v_snd_1114_ = lean_ctor_get(v_a_1112_, 1);
lean_inc(v_snd_1114_);
lean_dec(v_a_1112_);
v___x_1115_ = lean_apply_8(v_k_1102_, v_fst_1113_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, lean_box(0));
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1125_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1120_ = 1;
v___x_1121_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1120_, v_snd_1114_, v_a_1116_);
lean_dec(v_snd_1114_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1121_);
v___x_1123_ = v___x_1118_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_dec(v_snd_1114_);
return v___x_1115_;
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec_ref(v_k_1102_);
v_a_1126_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1111_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1111_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___boxed(lean_object* v_args_1134_, lean_object* v_ps_1135_, lean_object* v_k_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(v_args_1134_, v_ps_1135_, v_k_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec_ref(v_args_1134_);
return v_res_1144_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = lean_box(0);
v___x_1149_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1));
v___x_1150_ = l_Lean_Expr_const___override(v___x_1149_, v___x_1148_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(lean_object* v_x_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___boxed(lean_object* v_x_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(v_x_1153_);
lean_dec(v_x_1153_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(lean_object* v_args_1156_, lean_object* v_k_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v___f_1165_; lean_object* v___x_1166_; 
v___f_1165_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0));
lean_inc(v_a_1163_);
lean_inc_ref(v_a_1162_);
lean_inc(v_a_1161_);
lean_inc_ref(v_a_1160_);
lean_inc_ref(v_a_1158_);
v___x_1166_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1156_, v___f_1165_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v_fst_1168_; lean_object* v_snd_1169_; lean_object* v___x_1170_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref(v___x_1166_);
v_fst_1168_ = lean_ctor_get(v_a_1167_, 0);
lean_inc(v_fst_1168_);
v_snd_1169_ = lean_ctor_get(v_a_1167_, 1);
lean_inc(v_snd_1169_);
lean_dec(v_a_1167_);
v___x_1170_ = lean_apply_8(v_k_1157_, v_fst_1168_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, lean_box(0));
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1180_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1180_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1180_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1175_ = 1;
v___x_1176_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1175_, v_snd_1169_, v_a_1171_);
lean_dec(v_snd_1169_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1176_);
v___x_1178_ = v___x_1173_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
else
{
lean_dec(v_snd_1169_);
return v___x_1170_;
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec_ref(v_k_1157_);
v_a_1181_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1166_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1166_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___boxed(lean_object* v_args_1189_, lean_object* v_k_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(v_args_1189_, v_k_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
lean_dec_ref(v_args_1189_);
return v_res_1198_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0(void){
_start:
{
uint8_t v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = 1;
v___x_1200_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(lean_object* v_msg_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
v___x_1203_ = lean_panic_fn(v___x_1202_, v_msg_1201_);
return v___x_1203_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1207_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1208_ = lean_unsigned_to_nat(9u);
v___x_1209_ = lean_unsigned_to_nat(611u);
v___x_1210_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1));
v___x_1211_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0));
v___x_1212_ = l_mkPanicMessageWithDecl(v___x_1211_, v___x_1210_, v___x_1209_, v___x_1208_, v___x_1207_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(lean_object* v_code_1213_, lean_object* v_decl_1214_, lean_object* v_k_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
uint8_t v___y_1222_; lean_object* v_type_1226_; lean_object* v_value_1227_; uint8_t v___x_1228_; 
v_type_1226_ = lean_ctor_get(v_decl_1214_, 2);
v_value_1227_ = lean_ctor_get(v_decl_1214_, 3);
v___x_1228_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_1226_);
if (v___x_1228_ == 0)
{
if (lean_obj_tag(v_code_1213_) == 0)
{
lean_object* v_decl_1229_; lean_object* v_k_1230_; size_t v___x_1231_; size_t v___x_1232_; uint8_t v___x_1233_; 
v_decl_1229_ = lean_ctor_get(v_code_1213_, 0);
v_k_1230_ = lean_ctor_get(v_code_1213_, 1);
v___x_1231_ = lean_ptr_addr(v_k_1230_);
v___x_1232_ = lean_ptr_addr(v_k_1215_);
v___x_1233_ = lean_usize_dec_eq(v___x_1231_, v___x_1232_);
if (v___x_1233_ == 0)
{
v___y_1222_ = v___x_1233_;
goto v___jp_1221_;
}
else
{
size_t v___x_1234_; size_t v___x_1235_; uint8_t v___x_1236_; 
v___x_1234_ = lean_ptr_addr(v_decl_1229_);
v___x_1235_ = lean_ptr_addr(v_decl_1214_);
v___x_1236_ = lean_usize_dec_eq(v___x_1234_, v___x_1235_);
v___y_1222_ = v___x_1236_;
goto v___jp_1221_;
}
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec_ref(v_k_1215_);
lean_dec_ref(v_decl_1214_);
lean_dec_ref(v_code_1213_);
v___x_1237_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_1238_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_1237_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
}
else
{
uint8_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec_ref(v_code_1213_);
v___x_1240_ = 1;
v___x_1241_ = lean_box(0);
v___x_1242_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
lean_inc(v_value_1227_);
v___x_1243_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1240_, v___x_1241_, v___x_1242_, v_value_1227_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v_fvarId_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref(v___x_1243_);
v_fvarId_1245_ = lean_ctor_get(v_a_1244_, 0);
lean_inc(v_fvarId_1245_);
v___x_1246_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_1246_, 0, v_fvarId_1245_);
v___x_1247_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1240_, v_decl_1214_, v___x_1246_, v_a_1217_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1257_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1257_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1257_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_a_1248_);
lean_ctor_set(v___x_1252_, 1, v_k_1215_);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v_a_1244_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1253_);
v___x_1255_ = v___x_1250_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v_a_1244_);
lean_dec_ref(v_k_1215_);
v_a_1258_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1247_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1247_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_k_1215_);
lean_dec_ref(v_decl_1214_);
v_a_1266_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1243_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1243_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
v___jp_1221_:
{
if (v___y_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref(v_code_1213_);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_decl_1214_);
lean_ctor_set(v___x_1223_, 1, v_k_1215_);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
else
{
lean_object* v___x_1225_; 
lean_dec_ref(v_k_1215_);
lean_dec_ref(v_decl_1214_);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v_code_1213_);
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___boxed(lean_object* v_code_1274_, lean_object* v_decl_1275_, lean_object* v_k_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1274_, v_decl_1275_, v_k_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(lean_object* v_code_1283_, lean_object* v_decl_1284_, lean_object* v_k_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1283_, v_decl_1284_, v_k_1285_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___boxed(lean_object* v_code_1294_, lean_object* v_decl_1295_, lean_object* v_k_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(v_code_1294_, v_decl_1295_, v_k_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(lean_object* v_code_1305_, lean_object* v_decl_1306_, lean_object* v_expType_1307_, lean_object* v_k_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
uint8_t v___y_1317_; lean_object* v_type_1321_; lean_object* v_value_1322_; uint8_t v___x_1323_; 
v_type_1321_ = lean_ctor_get(v_decl_1306_, 2);
v_value_1322_ = lean_ctor_get(v_decl_1306_, 3);
v___x_1323_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_type_1321_, v_expType_1307_);
if (v___x_1323_ == 0)
{
lean_object* v_boxedTy_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_dec_ref(v_code_1305_);
v_boxedTy_1324_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_1321_);
v___x_1325_ = 1;
v___x_1326_ = lean_box(0);
lean_inc(v_value_1322_);
v___x_1327_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1325_, v___x_1326_, v_boxedTy_1324_, v_value_1322_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v_fvarId_1329_; lean_object* v_type_1330_; lean_object* v___x_1331_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref(v___x_1327_);
v_fvarId_1329_ = lean_ctor_get(v_a_1328_, 0);
v_type_1330_ = lean_ctor_get(v_a_1328_, 2);
lean_inc(v_a_1312_);
lean_inc_ref(v_type_1321_);
lean_inc_ref(v_type_1330_);
lean_inc(v_fvarId_1329_);
v___x_1331_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_1329_, v_type_1330_, v_type_1321_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1333_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec_ref(v___x_1331_);
v___x_1333_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1325_, v_decl_1306_, v_a_1332_, v_a_1312_);
lean_dec(v_a_1312_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1343_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_a_1334_);
lean_ctor_set(v___x_1338_, 1, v_k_1308_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_a_1328_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1339_);
v___x_1341_ = v___x_1336_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec(v_a_1328_);
lean_dec_ref(v_k_1308_);
v_a_1344_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1333_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1333_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec(v_a_1328_);
lean_dec(v_a_1312_);
lean_dec_ref(v_k_1308_);
lean_dec_ref(v_decl_1306_);
v_a_1352_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1331_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1331_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec_ref(v_a_1309_);
lean_dec_ref(v_k_1308_);
lean_dec_ref(v_decl_1306_);
v_a_1360_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1327_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1327_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec_ref(v_a_1309_);
if (lean_obj_tag(v_code_1305_) == 0)
{
lean_object* v_decl_1368_; lean_object* v_k_1369_; size_t v___x_1370_; size_t v___x_1371_; uint8_t v___x_1372_; 
v_decl_1368_ = lean_ctor_get(v_code_1305_, 0);
v_k_1369_ = lean_ctor_get(v_code_1305_, 1);
v___x_1370_ = lean_ptr_addr(v_k_1369_);
v___x_1371_ = lean_ptr_addr(v_k_1308_);
v___x_1372_ = lean_usize_dec_eq(v___x_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
v___y_1317_ = v___x_1372_;
goto v___jp_1316_;
}
else
{
size_t v___x_1373_; size_t v___x_1374_; uint8_t v___x_1375_; 
v___x_1373_ = lean_ptr_addr(v_decl_1368_);
v___x_1374_ = lean_ptr_addr(v_decl_1306_);
v___x_1375_ = lean_usize_dec_eq(v___x_1373_, v___x_1374_);
v___y_1317_ = v___x_1375_;
goto v___jp_1316_;
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec_ref(v_k_1308_);
lean_dec_ref(v_decl_1306_);
lean_dec_ref(v_code_1305_);
v___x_1376_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_1377_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_1376_);
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
return v___x_1378_;
}
}
v___jp_1316_:
{
if (v___y_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec_ref(v_code_1305_);
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v_decl_1306_);
lean_ctor_set(v___x_1318_, 1, v_k_1308_);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; 
lean_dec_ref(v_k_1308_);
lean_dec_ref(v_decl_1306_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_code_1305_);
return v___x_1320_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded___boxed(lean_object* v_code_1379_, lean_object* v_decl_1380_, lean_object* v_expType_1381_, lean_object* v_k_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(v_code_1379_, v_decl_1380_, v_expType_1381_, v_k_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_);
lean_dec(v_a_1384_);
lean_dec_ref(v_expType_1381_);
return v_res_1390_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(lean_object* v_msg_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_toApplicative_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1469_; 
v___x_1404_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
v___x_1405_ = l_ReaderT_instMonad___redArg(v___x_1404_);
v_toApplicative_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1405_, 1);
lean_dec(v_unused_1470_);
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1469_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_toApplicative_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1469_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_toFunctor_1410_; lean_object* v_toSeq_1411_; lean_object* v_toSeqLeft_1412_; lean_object* v_toSeqRight_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1467_; 
v_toFunctor_1410_ = lean_ctor_get(v_toApplicative_1406_, 0);
v_toSeq_1411_ = lean_ctor_get(v_toApplicative_1406_, 2);
v_toSeqLeft_1412_ = lean_ctor_get(v_toApplicative_1406_, 3);
v_toSeqRight_1413_ = lean_ctor_get(v_toApplicative_1406_, 4);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_toApplicative_1406_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v_toApplicative_1406_, 1);
lean_dec(v_unused_1468_);
v___x_1415_ = v_toApplicative_1406_;
v_isShared_1416_ = v_isSharedCheck_1467_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_toSeqRight_1413_);
lean_inc(v_toSeqLeft_1412_);
lean_inc(v_toSeq_1411_);
lean_inc(v_toFunctor_1410_);
lean_dec(v_toApplicative_1406_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1467_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___f_1417_; lean_object* v___f_1418_; lean_object* v___f_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; lean_object* v___f_1422_; lean_object* v___f_1423_; lean_object* v___f_1424_; lean_object* v___x_1426_; 
v___f_1417_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1));
v___f_1418_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1410_);
v___f_1419_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1419_, 0, v_toFunctor_1410_);
v___f_1420_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1420_, 0, v_toFunctor_1410_);
v___x_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___f_1419_);
lean_ctor_set(v___x_1421_, 1, v___f_1420_);
v___f_1422_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1422_, 0, v_toSeqRight_1413_);
v___f_1423_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1423_, 0, v_toSeqLeft_1412_);
v___f_1424_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1424_, 0, v_toSeq_1411_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v___f_1422_);
lean_ctor_set(v___x_1415_, 3, v___f_1423_);
lean_ctor_set(v___x_1415_, 2, v___f_1424_);
lean_ctor_set(v___x_1415_, 1, v___f_1417_);
lean_ctor_set(v___x_1415_, 0, v___x_1421_);
v___x_1426_ = v___x_1415_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___f_1417_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v___f_1424_);
lean_ctor_set(v_reuseFailAlloc_1466_, 3, v___f_1423_);
lean_ctor_set(v_reuseFailAlloc_1466_, 4, v___f_1422_);
v___x_1426_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1428_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v___f_1418_);
lean_ctor_set(v___x_1408_, 0, v___x_1426_);
v___x_1428_ = v___x_1408_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___f_1418_);
v___x_1428_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; lean_object* v_toApplicative_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1463_; 
v___x_1429_ = l_ReaderT_instMonad___redArg(v___x_1428_);
v_toApplicative_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v___x_1429_, 1);
lean_dec(v_unused_1464_);
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1463_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_toApplicative_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1463_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v_toFunctor_1434_; lean_object* v_toSeq_1435_; lean_object* v_toSeqLeft_1436_; lean_object* v_toSeqRight_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1461_; 
v_toFunctor_1434_ = lean_ctor_get(v_toApplicative_1430_, 0);
v_toSeq_1435_ = lean_ctor_get(v_toApplicative_1430_, 2);
v_toSeqLeft_1436_ = lean_ctor_get(v_toApplicative_1430_, 3);
v_toSeqRight_1437_ = lean_ctor_get(v_toApplicative_1430_, 4);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_toApplicative_1430_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_toApplicative_1430_, 1);
lean_dec(v_unused_1462_);
v___x_1439_ = v_toApplicative_1430_;
v_isShared_1440_ = v_isSharedCheck_1461_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_toSeqRight_1437_);
lean_inc(v_toSeqLeft_1436_);
lean_inc(v_toSeq_1435_);
lean_inc(v_toFunctor_1434_);
lean_dec(v_toApplicative_1430_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1461_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___f_1444_; lean_object* v___x_1445_; lean_object* v___f_1446_; lean_object* v___f_1447_; lean_object* v___f_1448_; lean_object* v___x_1450_; 
v___f_1441_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3));
v___f_1442_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1434_);
v___f_1443_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1443_, 0, v_toFunctor_1434_);
v___f_1444_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1444_, 0, v_toFunctor_1434_);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___f_1443_);
lean_ctor_set(v___x_1445_, 1, v___f_1444_);
v___f_1446_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1446_, 0, v_toSeqRight_1437_);
v___f_1447_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1447_, 0, v_toSeqLeft_1436_);
v___f_1448_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1448_, 0, v_toSeq_1435_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v___f_1446_);
lean_ctor_set(v___x_1439_, 3, v___f_1447_);
lean_ctor_set(v___x_1439_, 2, v___f_1448_);
lean_ctor_set(v___x_1439_, 1, v___f_1441_);
lean_ctor_set(v___x_1439_, 0, v___x_1445_);
v___x_1450_ = v___x_1439_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___f_1441_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v___f_1448_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v___f_1447_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v___f_1446_);
v___x_1450_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v___f_1442_);
lean_ctor_set(v___x_1432_, 0, v___x_1450_);
v___x_1452_ = v___x_1432_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___f_1442_);
v___x_1452_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___f_1456_; lean_object* v___x_3893__overap_1457_; lean_object* v___x_1458_; 
v___x_1453_ = l_ReaderT_instMonad___redArg(v___x_1452_);
v___x_1454_ = l_Lean_instInhabitedExpr;
v___x_1455_ = l_instInhabitedOfMonad___redArg(v___x_1453_, v___x_1454_);
v___f_1456_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1456_, 0, v___x_1455_);
v___x_3893__overap_1457_ = lean_panic_fn(v___f_1456_, v_msg_1396_);
v___x_1458_ = lean_apply_7(v___x_3893__overap_1457_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, lean_box(0));
return v___x_1458_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___boxed(lean_object* v_msg_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v_msg_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v_res_1479_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = lean_box(0);
v___x_1484_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1));
v___x_1485_ = l_Lean_Expr_const___override(v___x_1484_, v___x_1483_);
return v___x_1485_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = lean_box(0);
v___x_1490_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4));
v___x_1491_ = l_Lean_Expr_const___override(v___x_1490_, v___x_1489_);
return v___x_1491_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = lean_box(0);
v___x_1496_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7));
v___x_1497_ = l_Lean_Expr_const___override(v___x_1496_, v___x_1495_);
return v___x_1497_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1500_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1501_ = lean_unsigned_to_nat(45u);
v___x_1502_ = lean_unsigned_to_nat(301u);
v___x_1503_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10));
v___x_1504_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
v___x_1505_ = l_mkPanicMessageWithDecl(v___x_1504_, v___x_1503_, v___x_1502_, v___x_1501_, v___x_1500_);
return v___x_1505_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1506_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1507_ = lean_unsigned_to_nat(44u);
v___x_1508_ = lean_unsigned_to_nat(316u);
v___x_1509_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10));
v___x_1510_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
v___x_1511_ = l_mkPanicMessageWithDecl(v___x_1510_, v___x_1509_, v___x_1508_, v___x_1507_, v___x_1506_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(lean_object* v_currentType_1512_, lean_object* v_value_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
switch(lean_obj_tag(v_value_1513_))
{
case 0:
{
lean_object* v_value_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
v_value_1521_ = lean_ctor_get(v_value_1513_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_value_1513_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1523_ = v_value_1513_;
v_isShared_1524_ = v_isSharedCheck_1551_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_value_1521_);
lean_dec(v_value_1513_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1551_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
switch(lean_obj_tag(v_value_1521_))
{
case 0:
{
lean_object* v_val_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1538_; 
lean_del_object(v___x_1523_);
v_val_1525_ = lean_ctor_get(v_value_1521_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_value_1521_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1527_ = v_value_1521_;
v_isShared_1528_ = v_isSharedCheck_1538_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_val_1525_);
lean_dec(v_value_1521_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1538_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = l_Lean_maxSmallNat;
v___x_1530_ = lean_nat_dec_le(v_val_1525_, v___x_1529_);
lean_dec(v_val_1525_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1532_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v_currentType_1512_);
v___x_1532_ = v___x_1527_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_currentType_1512_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
else
{
lean_object* v___x_1534_; lean_object* v___x_1536_; 
lean_dec_ref(v_currentType_1512_);
v___x_1534_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1534_);
v___x_1536_ = v___x_1527_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
case 1:
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1546_; 
lean_del_object(v___x_1523_);
lean_dec_ref(v_currentType_1512_);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_value_1521_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v_value_1521_, 0);
lean_dec(v_unused_1547_);
v___x_1540_ = v_value_1521_;
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v_value_1521_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1542_);
v___x_1544_ = v___x_1540_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
default: 
{
lean_object* v___x_1549_; 
lean_dec_ref(v_value_1521_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v_currentType_1512_);
v___x_1549_ = v___x_1523_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_currentType_1512_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec_ref(v_currentType_1512_);
v___x_1552_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
case 5:
{
lean_object* v_i_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec_ref(v_currentType_1512_);
v_i_1554_ = lean_ctor_get(v_value_1513_, 0);
lean_inc_ref(v_i_1554_);
lean_dec_ref(v_value_1513_);
v___x_1555_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_i_1554_);
lean_dec_ref(v_i_1554_);
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
case 7:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec_ref(v_value_1513_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec_ref(v_currentType_1512_);
v___x_1557_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
return v___x_1558_;
}
case 9:
{
lean_object* v_fn_1559_; lean_object* v___x_1560_; 
lean_dec_ref(v_currentType_1512_);
v_fn_1559_ = lean_ctor_get(v_value_1513_, 0);
lean_inc(v_fn_1559_);
lean_dec_ref(v_value_1513_);
v___x_1560_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_1559_, v_a_1519_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1572_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1572_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1572_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
if (lean_obj_tag(v_a_1561_) == 1)
{
lean_object* v_val_1565_; lean_object* v_type_1566_; lean_object* v___x_1568_; 
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
v_val_1565_ = lean_ctor_get(v_a_1561_, 0);
lean_inc(v_val_1565_);
lean_dec_ref(v_a_1561_);
v_type_1566_ = lean_ctor_get(v_val_1565_, 2);
lean_inc_ref(v_type_1566_);
lean_dec(v_val_1565_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v_type_1566_);
v___x_1568_ = v___x_1563_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_type_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_del_object(v___x_1563_);
lean_dec(v_a_1561_);
v___x_1570_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11);
v___x_1571_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1570_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
return v___x_1571_;
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
v_a_1573_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1560_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1560_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
case 10:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_dec_ref(v_value_1513_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec_ref(v_currentType_1512_);
v___x_1581_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
case 13:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec_ref(v_value_1513_);
lean_dec_ref(v_currentType_1512_);
v___x_1583_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12);
v___x_1584_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1583_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
return v___x_1584_;
}
case 14:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec_ref(v_value_1513_);
lean_dec_ref(v_currentType_1512_);
v___x_1585_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12);
v___x_1586_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1585_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
return v___x_1586_;
}
case 15:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec_ref(v_value_1513_);
lean_dec_ref(v_currentType_1512_);
v___x_1587_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12);
v___x_1588_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1587_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
return v___x_1588_;
}
default: 
{
lean_object* v___x_1589_; 
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec(v_value_1513_);
v___x_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1589_, 0, v_currentType_1512_);
return v___x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___boxed(lean_object* v_currentType_1590_, lean_object* v_value_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(v_currentType_1590_, v_value_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(lean_object* v_msg_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v_toApplicative_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1673_; 
v___x_1608_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
v___x_1609_ = l_ReaderT_instMonad___redArg(v___x_1608_);
v_toApplicative_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v___x_1609_, 1);
lean_dec(v_unused_1674_);
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1673_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_toApplicative_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1673_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v_toFunctor_1614_; lean_object* v_toSeq_1615_; lean_object* v_toSeqLeft_1616_; lean_object* v_toSeqRight_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1671_; 
v_toFunctor_1614_ = lean_ctor_get(v_toApplicative_1610_, 0);
v_toSeq_1615_ = lean_ctor_get(v_toApplicative_1610_, 2);
v_toSeqLeft_1616_ = lean_ctor_get(v_toApplicative_1610_, 3);
v_toSeqRight_1617_ = lean_ctor_get(v_toApplicative_1610_, 4);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_toApplicative_1610_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; 
v_unused_1672_ = lean_ctor_get(v_toApplicative_1610_, 1);
lean_dec(v_unused_1672_);
v___x_1619_ = v_toApplicative_1610_;
v_isShared_1620_ = v_isSharedCheck_1671_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_toSeqRight_1617_);
lean_inc(v_toSeqLeft_1616_);
lean_inc(v_toSeq_1615_);
lean_inc(v_toFunctor_1614_);
lean_dec(v_toApplicative_1610_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1671_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___f_1621_; lean_object* v___f_1622_; lean_object* v___f_1623_; lean_object* v___f_1624_; lean_object* v___x_1625_; lean_object* v___f_1626_; lean_object* v___f_1627_; lean_object* v___f_1628_; lean_object* v___x_1630_; 
v___f_1621_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1));
v___f_1622_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1614_);
v___f_1623_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1623_, 0, v_toFunctor_1614_);
v___f_1624_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1624_, 0, v_toFunctor_1614_);
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___f_1623_);
lean_ctor_set(v___x_1625_, 1, v___f_1624_);
v___f_1626_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1626_, 0, v_toSeqRight_1617_);
v___f_1627_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1627_, 0, v_toSeqLeft_1616_);
v___f_1628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1628_, 0, v_toSeq_1615_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 4, v___f_1626_);
lean_ctor_set(v___x_1619_, 3, v___f_1627_);
lean_ctor_set(v___x_1619_, 2, v___f_1628_);
lean_ctor_set(v___x_1619_, 1, v___f_1621_);
lean_ctor_set(v___x_1619_, 0, v___x_1625_);
v___x_1630_ = v___x_1619_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___f_1621_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v___f_1628_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v___f_1627_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v___f_1626_);
v___x_1630_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1632_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 1, v___f_1622_);
lean_ctor_set(v___x_1612_, 0, v___x_1630_);
v___x_1632_ = v___x_1612_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v___f_1622_);
v___x_1632_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1633_; lean_object* v_toApplicative_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1667_; 
v___x_1633_ = l_ReaderT_instMonad___redArg(v___x_1632_);
v_toApplicative_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; 
v_unused_1668_ = lean_ctor_get(v___x_1633_, 1);
lean_dec(v_unused_1668_);
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1667_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_toApplicative_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1667_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v_toFunctor_1638_; lean_object* v_toSeq_1639_; lean_object* v_toSeqLeft_1640_; lean_object* v_toSeqRight_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1665_; 
v_toFunctor_1638_ = lean_ctor_get(v_toApplicative_1634_, 0);
v_toSeq_1639_ = lean_ctor_get(v_toApplicative_1634_, 2);
v_toSeqLeft_1640_ = lean_ctor_get(v_toApplicative_1634_, 3);
v_toSeqRight_1641_ = lean_ctor_get(v_toApplicative_1634_, 4);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_toApplicative_1634_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v_toApplicative_1634_, 1);
lean_dec(v_unused_1666_);
v___x_1643_ = v_toApplicative_1634_;
v_isShared_1644_ = v_isSharedCheck_1665_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_toSeqRight_1641_);
lean_inc(v_toSeqLeft_1640_);
lean_inc(v_toSeq_1639_);
lean_inc(v_toFunctor_1638_);
lean_dec(v_toApplicative_1634_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1665_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___f_1645_; lean_object* v___f_1646_; lean_object* v___f_1647_; lean_object* v___f_1648_; lean_object* v___x_1649_; lean_object* v___f_1650_; lean_object* v___f_1651_; lean_object* v___f_1652_; lean_object* v___x_1654_; 
v___f_1645_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3));
v___f_1646_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1638_);
v___f_1647_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1647_, 0, v_toFunctor_1638_);
v___f_1648_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1648_, 0, v_toFunctor_1638_);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___f_1647_);
lean_ctor_set(v___x_1649_, 1, v___f_1648_);
v___f_1650_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1650_, 0, v_toSeqRight_1641_);
v___f_1651_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1651_, 0, v_toSeqLeft_1640_);
v___f_1652_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1652_, 0, v_toSeq_1639_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 4, v___f_1650_);
lean_ctor_set(v___x_1643_, 3, v___f_1651_);
lean_ctor_set(v___x_1643_, 2, v___f_1652_);
lean_ctor_set(v___x_1643_, 1, v___f_1645_);
lean_ctor_set(v___x_1643_, 0, v___x_1649_);
v___x_1654_ = v___x_1643_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___f_1645_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v___f_1652_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v___f_1651_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v___f_1650_);
v___x_1654_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1656_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 1, v___f_1646_);
lean_ctor_set(v___x_1636_, 0, v___x_1654_);
v___x_1656_ = v___x_1636_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___f_1646_);
v___x_1656_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___f_1660_; lean_object* v___x_24861__overap_1661_; lean_object* v___x_1662_; 
v___x_1657_ = l_ReaderT_instMonad___redArg(v___x_1656_);
v___x_1658_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
v___x_1659_ = l_instInhabitedOfMonad___redArg(v___x_1657_, v___x_1658_);
v___f_1660_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1660_, 0, v___x_1659_);
v___x_24861__overap_1661_ = lean_panic_fn(v___f_1660_, v_msg_1600_);
v___x_1662_ = lean_apply_7(v___x_24861__overap_1661_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, lean_box(0));
return v___x_1662_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0___boxed(lean_object* v_msg_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v_msg_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(lean_object* v_x_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0___boxed(lean_object* v_x_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(v_x_1686_);
lean_dec(v_x_1686_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2(uint8_t v___x_1688_, lean_object* v_params_1689_, lean_object* v_i_1690_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v_type_1693_; 
v___x_1691_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_1688_);
v___x_1692_ = lean_array_get_borrowed(v___x_1691_, v_params_1689_, v_i_1690_);
v_type_1693_ = lean_ctor_get(v___x_1692_, 2);
lean_inc_ref(v_type_1693_);
return v_type_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2___boxed(lean_object* v___x_1694_, lean_object* v_params_1695_, lean_object* v_i_1696_){
_start:
{
uint8_t v___x_26046__boxed_1697_; lean_object* v_res_1698_; 
v___x_26046__boxed_1697_ = lean_unbox(v___x_1694_);
v_res_1698_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2(v___x_26046__boxed_1697_, v_params_1695_, v_i_1696_);
lean_dec(v_i_1696_);
lean_dec_ref(v_params_1695_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(lean_object* v_fvarId_1699_, lean_object* v_code_1700_, lean_object* v_fvarId_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v___x_1709_; 
v___x_1709_ = l_Lean_instBEqFVarId_beq(v_fvarId_1699_, v_fvarId_1701_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_dec_ref(v_code_1700_);
v___x_1710_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_fvarId_1701_);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; 
lean_dec(v_fvarId_1701_);
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v_code_1700_);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2___boxed(lean_object* v_fvarId_1713_, lean_object* v_code_1714_, lean_object* v_fvarId_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_1713_, v_code_1714_, v_fvarId_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v_fvarId_1713_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(lean_object* v_typeName_1724_, lean_object* v_a_1725_, lean_object* v_discr_1726_, lean_object* v_code_1727_, lean_object* v_alts_1728_, lean_object* v_resultType_1729_, lean_object* v_discr_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_currDeclResultType_1738_; uint8_t v___y_1744_; size_t v___x_1747_; size_t v___x_1748_; uint8_t v___x_1749_; 
v_currDeclResultType_1738_ = lean_ctor_get(v___y_1731_, 1);
v___x_1747_ = lean_ptr_addr(v_alts_1728_);
v___x_1748_ = lean_ptr_addr(v_a_1725_);
v___x_1749_ = lean_usize_dec_eq(v___x_1747_, v___x_1748_);
if (v___x_1749_ == 0)
{
v___y_1744_ = v___x_1749_;
goto v___jp_1743_;
}
else
{
size_t v___x_1750_; size_t v___x_1751_; uint8_t v___x_1752_; 
v___x_1750_ = lean_ptr_addr(v_resultType_1729_);
v___x_1751_ = lean_ptr_addr(v_currDeclResultType_1738_);
v___x_1752_ = lean_usize_dec_eq(v___x_1750_, v___x_1751_);
v___y_1744_ = v___x_1752_;
goto v___jp_1743_;
}
v___jp_1739_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_inc_ref(v_currDeclResultType_1738_);
v___x_1740_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1740_, 0, v_typeName_1724_);
lean_ctor_set(v___x_1740_, 1, v_currDeclResultType_1738_);
lean_ctor_set(v___x_1740_, 2, v_discr_1730_);
lean_ctor_set(v___x_1740_, 3, v_a_1725_);
v___x_1741_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
return v___x_1742_;
}
v___jp_1743_:
{
if (v___y_1744_ == 0)
{
lean_dec_ref(v_code_1727_);
goto v___jp_1739_;
}
else
{
uint8_t v___x_1745_; 
v___x_1745_ = l_Lean_instBEqFVarId_beq(v_discr_1726_, v_discr_1730_);
if (v___x_1745_ == 0)
{
lean_dec_ref(v_code_1727_);
goto v___jp_1739_;
}
else
{
lean_object* v___x_1746_; 
lean_dec(v_discr_1730_);
lean_dec_ref(v_a_1725_);
lean_dec(v_typeName_1724_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_code_1727_);
return v___x_1746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1___boxed(lean_object* v_typeName_1753_, lean_object* v_a_1754_, lean_object* v_discr_1755_, lean_object* v_code_1756_, lean_object* v_alts_1757_, lean_object* v_resultType_1758_, lean_object* v_discr_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_1753_, v_a_1754_, v_discr_1755_, v_code_1756_, v_alts_1757_, v_resultType_1758_, v_discr_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v_resultType_1758_);
lean_dec_ref(v_alts_1757_);
lean_dec(v_discr_1755_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(lean_object* v_alt_1768_, lean_object* v_f_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___y_1778_; 
switch(lean_obj_tag(v_alt_1768_))
{
case 0:
{
lean_object* v_code_1797_; 
v_code_1797_ = lean_ctor_get(v_alt_1768_, 2);
lean_inc_ref(v_code_1797_);
v___y_1778_ = v_code_1797_;
goto v___jp_1777_;
}
case 1:
{
lean_object* v_code_1798_; 
v_code_1798_ = lean_ctor_get(v_alt_1768_, 1);
lean_inc_ref(v_code_1798_);
v___y_1778_ = v_code_1798_;
goto v___jp_1777_;
}
default: 
{
lean_object* v_code_1799_; 
v_code_1799_ = lean_ctor_get(v_alt_1768_, 0);
lean_inc_ref(v_code_1799_);
v___y_1778_ = v_code_1799_;
goto v___jp_1777_;
}
}
v___jp_1777_:
{
lean_object* v___x_1779_; 
v___x_1779_ = lean_apply_8(v_f_1769_, v___y_1778_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, lean_box(0));
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1788_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1788_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1788_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1784_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1768_, v_a_1780_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1784_);
v___x_1786_ = v___x_1782_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v_alt_1768_);
v_a_1789_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1779_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1779_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg___boxed(lean_object* v_alt_1800_, lean_object* v_f_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_alt_1800_, v_f_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(lean_object* v_fvarId_1810_, lean_object* v_i_1811_, lean_object* v_offset_1812_, lean_object* v_ty_1813_, lean_object* v_a_1814_, lean_object* v_y_1815_, lean_object* v_k_1816_, lean_object* v_code_1817_, lean_object* v_y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
uint8_t v___y_1827_; size_t v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = lean_ptr_addr(v_fvarId_1810_);
v___x_1849_ = lean_usize_dec_eq(v___x_1848_, v___x_1848_);
if (v___x_1849_ == 0)
{
v___y_1827_ = v___x_1849_;
goto v___jp_1826_;
}
else
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_nat_dec_eq(v_i_1811_, v_i_1811_);
v___y_1827_ = v___x_1850_;
goto v___jp_1826_;
}
v___jp_1826_:
{
if (v___y_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec_ref(v_code_1817_);
v___x_1828_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1828_, 0, v_fvarId_1810_);
lean_ctor_set(v___x_1828_, 1, v_i_1811_);
lean_ctor_set(v___x_1828_, 2, v_offset_1812_);
lean_ctor_set(v___x_1828_, 3, v_y_1818_);
lean_ctor_set(v___x_1828_, 4, v_ty_1813_);
lean_ctor_set(v___x_1828_, 5, v_a_1814_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
else
{
uint8_t v___x_1830_; 
v___x_1830_ = lean_nat_dec_eq(v_offset_1812_, v_offset_1812_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec_ref(v_code_1817_);
v___x_1831_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1831_, 0, v_fvarId_1810_);
lean_ctor_set(v___x_1831_, 1, v_i_1811_);
lean_ctor_set(v___x_1831_, 2, v_offset_1812_);
lean_ctor_set(v___x_1831_, 3, v_y_1818_);
lean_ctor_set(v___x_1831_, 4, v_ty_1813_);
lean_ctor_set(v___x_1831_, 5, v_a_1814_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
return v___x_1832_;
}
else
{
size_t v___x_1833_; size_t v___x_1834_; uint8_t v___x_1835_; 
v___x_1833_ = lean_ptr_addr(v_y_1815_);
v___x_1834_ = lean_ptr_addr(v_y_1818_);
v___x_1835_ = lean_usize_dec_eq(v___x_1833_, v___x_1834_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_dec_ref(v_code_1817_);
v___x_1836_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1836_, 0, v_fvarId_1810_);
lean_ctor_set(v___x_1836_, 1, v_i_1811_);
lean_ctor_set(v___x_1836_, 2, v_offset_1812_);
lean_ctor_set(v___x_1836_, 3, v_y_1818_);
lean_ctor_set(v___x_1836_, 4, v_ty_1813_);
lean_ctor_set(v___x_1836_, 5, v_a_1814_);
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
return v___x_1837_;
}
else
{
size_t v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_ptr_addr(v_ty_1813_);
v___x_1839_ = lean_usize_dec_eq(v___x_1838_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec_ref(v_code_1817_);
v___x_1840_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1840_, 0, v_fvarId_1810_);
lean_ctor_set(v___x_1840_, 1, v_i_1811_);
lean_ctor_set(v___x_1840_, 2, v_offset_1812_);
lean_ctor_set(v___x_1840_, 3, v_y_1818_);
lean_ctor_set(v___x_1840_, 4, v_ty_1813_);
lean_ctor_set(v___x_1840_, 5, v_a_1814_);
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
return v___x_1841_;
}
else
{
size_t v___x_1842_; size_t v___x_1843_; uint8_t v___x_1844_; 
v___x_1842_ = lean_ptr_addr(v_k_1816_);
v___x_1843_ = lean_ptr_addr(v_a_1814_);
v___x_1844_ = lean_usize_dec_eq(v___x_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec_ref(v_code_1817_);
v___x_1845_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1845_, 0, v_fvarId_1810_);
lean_ctor_set(v___x_1845_, 1, v_i_1811_);
lean_ctor_set(v___x_1845_, 2, v_offset_1812_);
lean_ctor_set(v___x_1845_, 3, v_y_1818_);
lean_ctor_set(v___x_1845_, 4, v_ty_1813_);
lean_ctor_set(v___x_1845_, 5, v_a_1814_);
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; 
lean_dec(v_y_1818_);
lean_dec_ref(v_a_1814_);
lean_dec_ref(v_ty_1813_);
lean_dec(v_offset_1812_);
lean_dec(v_i_1811_);
lean_dec(v_fvarId_1810_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_code_1817_);
return v___x_1847_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4___boxed(lean_object* v_fvarId_1851_, lean_object* v_i_1852_, lean_object* v_offset_1853_, lean_object* v_ty_1854_, lean_object* v_a_1855_, lean_object* v_y_1856_, lean_object* v_k_1857_, lean_object* v_code_1858_, lean_object* v_y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_1851_, v_i_1852_, v_offset_1853_, v_ty_1854_, v_a_1855_, v_y_1856_, v_k_1857_, v_code_1858_, v_y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec_ref(v_k_1857_);
lean_dec(v_y_1856_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(lean_object* v_fvarId_1868_, lean_object* v_i_1869_, lean_object* v_a_1870_, lean_object* v_y_1871_, lean_object* v_k_1872_, lean_object* v_code_1873_, lean_object* v_y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
uint8_t v___y_1883_; size_t v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = lean_ptr_addr(v_fvarId_1868_);
v___x_1898_ = lean_usize_dec_eq(v___x_1897_, v___x_1897_);
if (v___x_1898_ == 0)
{
v___y_1883_ = v___x_1898_;
goto v___jp_1882_;
}
else
{
uint8_t v___x_1899_; 
v___x_1899_ = lean_nat_dec_eq(v_i_1869_, v_i_1869_);
v___y_1883_ = v___x_1899_;
goto v___jp_1882_;
}
v___jp_1882_:
{
if (v___y_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec_ref(v_code_1873_);
v___x_1884_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1884_, 0, v_fvarId_1868_);
lean_ctor_set(v___x_1884_, 1, v_i_1869_);
lean_ctor_set(v___x_1884_, 2, v_y_1874_);
lean_ctor_set(v___x_1884_, 3, v_a_1870_);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
else
{
size_t v___x_1886_; size_t v___x_1887_; uint8_t v___x_1888_; 
v___x_1886_ = lean_ptr_addr(v_y_1871_);
v___x_1887_ = lean_ptr_addr(v_y_1874_);
v___x_1888_ = lean_usize_dec_eq(v___x_1886_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec_ref(v_code_1873_);
v___x_1889_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1889_, 0, v_fvarId_1868_);
lean_ctor_set(v___x_1889_, 1, v_i_1869_);
lean_ctor_set(v___x_1889_, 2, v_y_1874_);
lean_ctor_set(v___x_1889_, 3, v_a_1870_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
else
{
size_t v___x_1891_; size_t v___x_1892_; uint8_t v___x_1893_; 
v___x_1891_ = lean_ptr_addr(v_k_1872_);
v___x_1892_ = lean_ptr_addr(v_a_1870_);
v___x_1893_ = lean_usize_dec_eq(v___x_1891_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec_ref(v_code_1873_);
v___x_1894_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1894_, 0, v_fvarId_1868_);
lean_ctor_set(v___x_1894_, 1, v_i_1869_);
lean_ctor_set(v___x_1894_, 2, v_y_1874_);
lean_ctor_set(v___x_1894_, 3, v_a_1870_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; 
lean_dec(v_y_1874_);
lean_dec_ref(v_a_1870_);
lean_dec(v_i_1869_);
lean_dec(v_fvarId_1868_);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v_code_1873_);
return v___x_1896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3___boxed(lean_object* v_fvarId_1900_, lean_object* v_i_1901_, lean_object* v_a_1902_, lean_object* v_y_1903_, lean_object* v_k_1904_, lean_object* v_code_1905_, lean_object* v_y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_1900_, v_i_1901_, v_a_1902_, v_y_1903_, v_k_1904_, v_code_1905_, v_y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v_k_1904_);
lean_dec(v_y_1903_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(uint8_t v___x_1915_, lean_object* v_params_1916_, lean_object* v_i_1917_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v_type_1920_; 
v___x_1918_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_1915_);
v___x_1919_ = lean_array_get_borrowed(v___x_1918_, v_params_1916_, v_i_1917_);
v_type_1920_ = lean_ctor_get(v___x_1919_, 2);
lean_inc_ref(v_type_1920_);
return v_type_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed(lean_object* v___x_1921_, lean_object* v_params_1922_, lean_object* v_i_1923_){
_start:
{
uint8_t v___x_26383__boxed_1924_; lean_object* v_res_1925_; 
v___x_26383__boxed_1924_ = lean_unbox(v___x_1921_);
v_res_1925_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(v___x_26383__boxed_1924_, v_params_1922_, v_i_1923_);
lean_dec(v_i_1923_);
lean_dec_ref(v_params_1922_);
return v_res_1925_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1928_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1929_ = lean_unsigned_to_nat(45u);
v___x_1930_ = lean_unsigned_to_nat(336u);
v___x_1931_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1));
v___x_1932_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
v___x_1933_ = l_mkPanicMessageWithDecl(v___x_1932_, v___x_1931_, v___x_1930_, v___x_1929_, v___x_1928_);
return v___x_1933_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1934_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1935_ = lean_unsigned_to_nat(45u);
v___x_1936_ = lean_unsigned_to_nat(341u);
v___x_1937_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1));
v___x_1938_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
v___x_1939_ = l_mkPanicMessageWithDecl(v___x_1938_, v___x_1937_, v___x_1936_, v___x_1935_, v___x_1934_);
return v___x_1939_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1940_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1941_ = lean_unsigned_to_nat(44u);
v___x_1942_ = lean_unsigned_to_nat(353u);
v___x_1943_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1));
v___x_1944_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
v___x_1945_ = l_mkPanicMessageWithDecl(v___x_1944_, v___x_1943_, v___x_1942_, v___x_1941_, v___x_1940_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(lean_object* v_code_1946_, lean_object* v_decl_1947_, lean_object* v_k_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_type_1956_; lean_object* v_value_1957_; lean_object* v___x_1958_; 
v_type_1956_ = lean_ctor_get(v_decl_1947_, 2);
v_value_1957_ = lean_ctor_get(v_decl_1947_, 3);
lean_inc(v_value_1957_);
lean_inc(v_a_1954_);
lean_inc_ref(v_a_1953_);
lean_inc(v_a_1952_);
lean_inc_ref(v_a_1951_);
lean_inc(v_a_1950_);
lean_inc_ref(v_a_1949_);
lean_inc(v_value_1957_);
lean_inc_ref(v_type_1956_);
v___x_1958_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(v_type_1956_, v_value_1957_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_2334_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_2334_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_2334_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
uint8_t v___x_1963_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___x_1976_; 
v___x_1963_ = 1;
lean_inc(v_a_1959_);
v___x_1976_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_1963_, v_decl_1947_, v_a_1959_, v_value_1957_, v_a_1952_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2325_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_1979_ = v___x_1976_;
v_isShared_1980_ = v_isSharedCheck_2325_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1976_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2325_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; 
lean_inc(v_a_1954_);
lean_inc_ref(v_a_1953_);
lean_inc(v_a_1952_);
lean_inc_ref(v_a_1951_);
lean_inc(v_a_1950_);
lean_inc_ref(v_a_1949_);
v___x_1981_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2324_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_2324_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2324_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___y_1987_; lean_object* v___y_1988_; uint8_t v___y_1989_; lean_object* v___y_1992_; uint8_t v___y_1993_; lean_object* v___y_2002_; lean_object* v___y_2003_; uint8_t v___y_2004_; lean_object* v_value_2006_; 
v_value_2006_ = lean_ctor_get(v_a_1977_, 3);
switch(lean_obj_tag(v_value_2006_))
{
case 4:
{
lean_object* v_args_2007_; lean_object* v___f_2008_; lean_object* v___x_2009_; 
lean_del_object(v___x_1984_);
lean_del_object(v___x_1979_);
lean_del_object(v___x_1961_);
lean_dec(v_a_1959_);
v_args_2007_ = lean_ctor_get(v_value_2006_, 1);
v___f_2008_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
lean_inc(v_a_1954_);
lean_inc_ref(v_a_1953_);
lean_inc(v_a_1952_);
lean_inc_ref(v_a_1951_);
v___x_2009_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2007_, v___f_2008_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1950_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v_fst_2011_; lean_object* v_snd_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref(v___x_2009_);
v_fst_2011_ = lean_ctor_get(v_a_2010_, 0);
lean_inc(v_fst_2011_);
v_snd_2012_ = lean_ctor_get(v_a_2010_, 1);
lean_inc(v_snd_2012_);
lean_dec(v_a_2010_);
lean_inc_ref(v_value_2006_);
v___x_2013_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_1963_, v_value_2006_, v_fst_2011_);
v___x_2014_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1963_, v_a_1977_, v___x_2013_, v_a_1952_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref(v___x_2014_);
v___x_2016_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1946_, v_a_2015_, v_a_1982_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2025_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1963_, v_snd_2012_, v_a_2017_);
lean_dec(v_snd_2012_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2021_);
v___x_2023_ = v___x_2019_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
else
{
lean_dec(v_snd_2012_);
return v___x_2016_;
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_snd_2012_);
lean_dec(v_a_1982_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec_ref(v_code_1946_);
v_a_2026_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2014_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2014_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec(v_a_1982_);
lean_dec(v_a_1977_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec_ref(v_code_1946_);
v_a_2034_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2009_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2009_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
case 5:
{
lean_object* v_i_2042_; lean_object* v_args_2043_; lean_object* v___f_2044_; uint8_t v___y_2046_; uint8_t v___x_2111_; 
lean_del_object(v___x_1979_);
v_i_2042_ = lean_ctor_get(v_value_2006_, 0);
v_args_2043_ = lean_ctor_get(v_value_2006_, 1);
v___f_2044_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_2111_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_i_2042_);
if (v___x_2111_ == 0)
{
v___y_2046_ = v___x_2111_;
goto v___jp_2045_;
}
else
{
uint8_t v___x_2112_; 
v___x_2112_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_1959_);
v___y_2046_ = v___x_2112_;
goto v___jp_2045_;
}
v___jp_2045_:
{
if (v___y_2046_ == 0)
{
lean_object* v___x_2047_; 
lean_del_object(v___x_1984_);
lean_dec(v_a_1959_);
lean_inc(v_a_1952_);
v___x_2047_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2043_, v___f_2044_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1950_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v_fst_2049_; lean_object* v_snd_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref(v___x_2047_);
v_fst_2049_ = lean_ctor_get(v_a_2048_, 0);
lean_inc(v_fst_2049_);
v_snd_2050_ = lean_ctor_get(v_a_2048_, 1);
lean_inc(v_snd_2050_);
lean_dec(v_a_2048_);
lean_inc_ref(v_value_2006_);
v___x_2051_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_1963_, v_value_2006_, v_fst_2049_);
v___x_2052_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1963_, v_a_1977_, v___x_2051_, v_a_1952_);
lean_dec(v_a_1952_);
if (lean_obj_tag(v___x_2052_) == 0)
{
if (lean_obj_tag(v_code_1946_) == 0)
{
lean_object* v_a_2053_; lean_object* v_decl_2054_; lean_object* v_k_2055_; size_t v___x_2056_; size_t v___x_2057_; uint8_t v___x_2058_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref(v___x_2052_);
v_decl_2054_ = lean_ctor_get(v_code_1946_, 0);
v_k_2055_ = lean_ctor_get(v_code_1946_, 1);
v___x_2056_ = lean_ptr_addr(v_k_2055_);
v___x_2057_ = lean_ptr_addr(v_a_1982_);
v___x_2058_ = lean_usize_dec_eq(v___x_2056_, v___x_2057_);
if (v___x_2058_ == 0)
{
v___y_2002_ = v_a_2053_;
v___y_2003_ = v_snd_2050_;
v___y_2004_ = v___x_2058_;
goto v___jp_2001_;
}
else
{
size_t v___x_2059_; size_t v___x_2060_; uint8_t v___x_2061_; 
v___x_2059_ = lean_ptr_addr(v_decl_2054_);
v___x_2060_ = lean_ptr_addr(v_a_2053_);
v___x_2061_ = lean_usize_dec_eq(v___x_2059_, v___x_2060_);
v___y_2002_ = v_a_2053_;
v___y_2003_ = v_snd_2050_;
v___y_2004_ = v___x_2061_;
goto v___jp_2001_;
}
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec_ref(v___x_2052_);
lean_dec(v_a_1982_);
lean_dec_ref(v_code_1946_);
v___x_2062_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2063_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2062_);
v___y_1965_ = v_snd_2050_;
v___y_1966_ = v___x_2063_;
goto v___jp_1964_;
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_snd_2050_);
lean_dec(v_a_1982_);
lean_del_object(v___x_1961_);
lean_dec_ref(v_code_1946_);
v_a_2064_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2052_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2052_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_a_1982_);
lean_dec(v_a_1977_);
lean_del_object(v___x_1961_);
lean_dec(v_a_1952_);
lean_dec_ref(v_code_1946_);
v_a_2072_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2047_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2047_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v_cidx_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_del_object(v___x_1961_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
v_cidx_2080_ = lean_ctor_get(v_i_2042_, 1);
v___x_2081_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_1959_, v_cidx_2080_);
lean_dec(v_a_1959_);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
v___x_2083_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1963_, v_a_1977_, v___x_2082_, v_a_1952_);
lean_dec(v_a_1952_);
if (lean_obj_tag(v___x_2083_) == 0)
{
if (lean_obj_tag(v_code_1946_) == 0)
{
lean_object* v_a_2084_; lean_object* v_decl_2085_; lean_object* v_k_2086_; size_t v___x_2087_; size_t v___x_2088_; uint8_t v___x_2089_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2083_);
v_decl_2085_ = lean_ctor_get(v_code_1946_, 0);
v_k_2086_ = lean_ctor_get(v_code_1946_, 1);
v___x_2087_ = lean_ptr_addr(v_k_2086_);
v___x_2088_ = lean_ptr_addr(v_a_1982_);
v___x_2089_ = lean_usize_dec_eq(v___x_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
v___y_1992_ = v_a_2084_;
v___y_1993_ = v___x_2089_;
goto v___jp_1991_;
}
else
{
size_t v___x_2090_; size_t v___x_2091_; uint8_t v___x_2092_; 
v___x_2090_ = lean_ptr_addr(v_decl_2085_);
v___x_2091_ = lean_ptr_addr(v_a_2084_);
v___x_2092_ = lean_usize_dec_eq(v___x_2090_, v___x_2091_);
v___y_1992_ = v_a_2084_;
v___y_1993_ = v___x_2092_;
goto v___jp_1991_;
}
}
else
{
lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2101_; 
lean_del_object(v___x_1984_);
lean_dec(v_a_1982_);
lean_dec_ref(v_code_1946_);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; 
v_unused_2102_ = lean_ctor_get(v___x_2083_, 0);
lean_dec(v_unused_2102_);
v___x_2094_ = v___x_2083_;
v_isShared_2095_ = v_isSharedCheck_2101_;
goto v_resetjp_2093_;
}
else
{
lean_dec(v___x_2083_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2101_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2096_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2097_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2096_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2097_);
v___x_2099_ = v___x_2094_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_del_object(v___x_1984_);
lean_dec(v_a_1982_);
lean_dec_ref(v_code_1946_);
v_a_2103_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2083_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2083_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
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
case 9:
{
lean_object* v_fn_2113_; lean_object* v_args_2114_; lean_object* v___x_2115_; 
lean_del_object(v___x_1984_);
lean_del_object(v___x_1979_);
lean_del_object(v___x_1961_);
lean_dec(v_a_1959_);
v_fn_2113_ = lean_ctor_get(v_value_2006_, 0);
v_args_2114_ = lean_ctor_get(v_value_2006_, 1);
lean_inc(v_fn_2113_);
v___x_2115_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_2113_, v_a_1954_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
if (lean_obj_tag(v_a_2116_) == 1)
{
lean_object* v_val_2117_; lean_object* v_type_2118_; lean_object* v_params_2119_; lean_object* v___x_2120_; lean_object* v___f_2121_; lean_object* v___x_2122_; 
v_val_2117_ = lean_ctor_get(v_a_2116_, 0);
lean_inc(v_val_2117_);
lean_dec_ref(v_a_2116_);
v_type_2118_ = lean_ctor_get(v_val_2117_, 2);
lean_inc_ref(v_type_2118_);
v_params_2119_ = lean_ctor_get(v_val_2117_, 3);
lean_inc_ref(v_params_2119_);
lean_dec(v_val_2117_);
v___x_2120_ = lean_box(v___x_1963_);
v___f_2121_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2___boxed), 3, 2);
lean_closure_set(v___f_2121_, 0, v___x_2120_);
lean_closure_set(v___f_2121_, 1, v_params_2119_);
lean_inc(v_a_1954_);
lean_inc_ref(v_a_1953_);
lean_inc(v_a_1952_);
lean_inc_ref(v_a_1951_);
lean_inc_ref(v_a_1949_);
v___x_2122_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2114_, v___f_2121_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v_fst_2124_; lean_object* v_snd_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref(v___x_2122_);
v_fst_2124_ = lean_ctor_get(v_a_2123_, 0);
lean_inc(v_fst_2124_);
v_snd_2125_ = lean_ctor_get(v_a_2123_, 1);
lean_inc(v_snd_2125_);
lean_dec(v_a_2123_);
lean_inc_ref(v_value_2006_);
v___x_2126_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_1963_, v_value_2006_, v_fst_2124_);
v___x_2127_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1963_, v_a_1977_, v___x_2126_, v_a_1952_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref(v___x_2127_);
v___x_2129_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(v_code_1946_, v_a_2128_, v_type_2118_, v_a_1982_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1950_);
lean_dec_ref(v_type_2118_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2138_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2134_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1963_, v_snd_2125_, v_a_2130_);
lean_dec(v_snd_2125_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2134_);
v___x_2136_ = v___x_2132_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
else
{
lean_dec(v_snd_2125_);
return v___x_2129_;
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec(v_snd_2125_);
lean_dec_ref(v_type_2118_);
lean_dec(v_a_1982_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec_ref(v_code_1946_);
v_a_2139_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2127_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2127_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref(v_type_2118_);
lean_dec(v_a_1982_);
lean_dec(v_a_1977_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec_ref(v_code_1946_);
v_a_2147_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2122_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2122_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
lean_dec(v_a_2116_);
lean_dec(v_a_1982_);
lean_dec(v_a_1977_);
lean_dec_ref(v_code_1946_);
v___x_2155_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2);
v___x_2156_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2155_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
return v___x_2156_;
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_a_1982_);
lean_dec(v_a_1977_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec_ref(v_code_1946_);
v_a_2157_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2115_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2115_);
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
case 10:
{
lean_object* v_fn_2165_; lean_object* v_args_2166_; lean_object* v___x_2167_; 
lean_del_object(v___x_1984_);
lean_del_object(v___x_1979_);
lean_del_object(v___x_1961_);
lean_dec(v_a_1959_);
v_fn_2165_ = lean_ctor_get(v_value_2006_, 0);
v_args_2166_ = lean_ctor_get(v_value_2006_, 1);
lean_inc(v_fn_2165_);
v___x_2167_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_2165_, v_a_1954_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref(v___x_2167_);
if (lean_obj_tag(v_a_2168_) == 1)
{
lean_object* v_val_2169_; lean_object* v___x_2170_; 
v_val_2169_ = lean_ctor_get(v_a_2168_, 0);
lean_inc(v_val_2169_);
lean_dec_ref(v_a_2168_);
v___x_2170_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_val_2169_, v_a_1954_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___f_2172_; lean_object* v___y_2174_; uint8_t v___x_2208_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref(v___x_2170_);
v___f_2172_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_2208_ = lean_unbox(v_a_2171_);
lean_dec(v_a_2171_);
if (v___x_2208_ == 0)
{
lean_inc(v_fn_2165_);
v___y_2174_ = v_fn_2165_;
goto v___jp_2173_;
}
else
{
lean_object* v___x_2209_; 
lean_inc(v_fn_2165_);
v___x_2209_ = l_Lean_Compiler_LCNF_mkBoxedName(v_fn_2165_);
v___y_2174_ = v___x_2209_;
goto v___jp_2173_;
}
v___jp_2173_:
{
lean_object* v___x_2175_; 
lean_inc(v_a_1952_);
v___x_2175_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2166_, v___f_2172_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1950_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v_fst_2177_; lean_object* v_snd_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref(v___x_2175_);
v_fst_2177_ = lean_ctor_get(v_a_2176_, 0);
lean_inc(v_fst_2177_);
v_snd_2178_ = lean_ctor_get(v_a_2176_, 1);
lean_inc(v_snd_2178_);
lean_dec(v_a_2176_);
v___x_2179_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updatePapImp(v___x_1963_, v_value_2006_, v___y_2174_, v_fst_2177_);
v___x_2180_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1963_, v_a_1977_, v___x_2179_, v_a_1952_);
lean_dec(v_a_1952_);
if (lean_obj_tag(v___x_2180_) == 0)
{
if (lean_obj_tag(v_code_1946_) == 0)
{
lean_object* v_a_2181_; lean_object* v_decl_2182_; lean_object* v_k_2183_; size_t v___x_2184_; size_t v___x_2185_; uint8_t v___x_2186_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref(v___x_2180_);
v_decl_2182_ = lean_ctor_get(v_code_1946_, 0);
v_k_2183_ = lean_ctor_get(v_code_1946_, 1);
v___x_2184_ = lean_ptr_addr(v_k_2183_);
v___x_2185_ = lean_ptr_addr(v_a_1982_);
v___x_2186_ = lean_usize_dec_eq(v___x_2184_, v___x_2185_);
if (v___x_2186_ == 0)
{
v___y_1987_ = v_snd_2178_;
v___y_1988_ = v_a_2181_;
v___y_1989_ = v___x_2186_;
goto v___jp_1986_;
}
else
{
size_t v___x_2187_; size_t v___x_2188_; uint8_t v___x_2189_; 
v___x_2187_ = lean_ptr_addr(v_decl_2182_);
v___x_2188_ = lean_ptr_addr(v_a_2181_);
v___x_2189_ = lean_usize_dec_eq(v___x_2187_, v___x_2188_);
v___y_1987_ = v_snd_2178_;
v___y_1988_ = v_a_2181_;
v___y_1989_ = v___x_2189_;
goto v___jp_1986_;
}
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec_ref(v___x_2180_);
lean_dec(v_a_1982_);
lean_dec_ref(v_code_1946_);
v___x_2190_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2191_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2190_);
v___y_1972_ = v_snd_2178_;
v___y_1973_ = v___x_2191_;
goto v___jp_1971_;
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_snd_2178_);
lean_dec(v_a_1982_);
lean_dec_ref(v_code_1946_);
v_a_2192_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2180_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2180_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v___y_2174_);
lean_dec(v_a_1982_);
lean_dec(v_a_1977_);
lean_dec(v_a_1952_);
lean_dec_ref(v_code_1946_);
v_a_2200_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2175_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2175_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_a_1982_);
lean_dec(v_a_1977_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec_ref(v_code_1946_);
v_a_2210_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2170_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2170_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec(v_a_2168_);
lean_dec(v_a_1982_);
lean_dec(v_a_1977_);
lean_dec_ref(v_code_1946_);
v___x_2218_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3);
v___x_2219_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2218_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
return v___x_2219_;
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_a_1982_);
lean_dec(v_a_1977_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec_ref(v_code_1946_);
v_a_2220_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2167_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2167_);
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
case 12:
{
lean_object* v_args_2228_; lean_object* v___f_2229_; lean_object* v___x_2230_; 
lean_del_object(v___x_1984_);
lean_del_object(v___x_1979_);
lean_del_object(v___x_1961_);
lean_dec(v_a_1959_);
v_args_2228_ = lean_ctor_get(v_value_2006_, 2);
v___f_2229_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
lean_inc(v_a_1952_);
v___x_2230_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2228_, v___f_2229_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1950_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v_fst_2232_; lean_object* v_snd_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2273_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref(v___x_2230_);
v_fst_2232_ = lean_ctor_get(v_a_2231_, 0);
v_snd_2233_ = lean_ctor_get(v_a_2231_, 1);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_a_2231_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2235_ = v_a_2231_;
v_isShared_2236_ = v_isSharedCheck_2273_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_snd_2233_);
lean_inc(v_fst_2232_);
lean_dec(v_a_2231_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2273_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_inc_ref(v_value_2006_);
v___x_2237_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_1963_, v_value_2006_, v_fst_2232_);
v___x_2238_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1963_, v_a_1977_, v___x_2237_, v_a_1952_);
lean_dec(v_a_1952_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2264_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2264_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2264_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___y_2244_; uint8_t v___y_2250_; 
if (lean_obj_tag(v_code_1946_) == 0)
{
lean_object* v_decl_2254_; lean_object* v_k_2255_; size_t v___x_2256_; size_t v___x_2257_; uint8_t v___x_2258_; 
v_decl_2254_ = lean_ctor_get(v_code_1946_, 0);
v_k_2255_ = lean_ctor_get(v_code_1946_, 1);
v___x_2256_ = lean_ptr_addr(v_k_2255_);
v___x_2257_ = lean_ptr_addr(v_a_1982_);
v___x_2258_ = lean_usize_dec_eq(v___x_2256_, v___x_2257_);
if (v___x_2258_ == 0)
{
v___y_2250_ = v___x_2258_;
goto v___jp_2249_;
}
else
{
size_t v___x_2259_; size_t v___x_2260_; uint8_t v___x_2261_; 
v___x_2259_ = lean_ptr_addr(v_decl_2254_);
v___x_2260_ = lean_ptr_addr(v_a_2239_);
v___x_2261_ = lean_usize_dec_eq(v___x_2259_, v___x_2260_);
v___y_2250_ = v___x_2261_;
goto v___jp_2249_;
}
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec(v_a_2239_);
lean_del_object(v___x_2235_);
lean_dec(v_a_1982_);
lean_dec_ref(v_code_1946_);
v___x_2262_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2263_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2262_);
v___y_2244_ = v___x_2263_;
goto v___jp_2243_;
}
v___jp_2243_:
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1963_, v_snd_2233_, v___y_2244_);
lean_dec(v_snd_2233_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2245_);
v___x_2247_ = v___x_2241_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
v___jp_2249_:
{
if (v___y_2250_ == 0)
{
lean_object* v___x_2252_; 
lean_dec_ref(v_code_1946_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 1, v_a_1982_);
lean_ctor_set(v___x_2235_, 0, v_a_2239_);
v___x_2252_ = v___x_2235_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2239_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_a_1982_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
v___y_2244_ = v___x_2252_;
goto v___jp_2243_;
}
}
else
{
lean_dec(v_a_2239_);
lean_del_object(v___x_2235_);
lean_dec(v_a_1982_);
v___y_2244_ = v_code_1946_;
goto v___jp_2243_;
}
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_del_object(v___x_2235_);
lean_dec(v_snd_2233_);
lean_dec(v_a_1982_);
lean_dec_ref(v_code_1946_);
v_a_2265_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2238_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2238_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_a_1982_);
lean_dec(v_a_1977_);
lean_dec(v_a_1952_);
lean_dec_ref(v_code_1946_);
v_a_2274_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2230_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2230_);
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
case 13:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
lean_del_object(v___x_1984_);
lean_dec(v_a_1982_);
lean_del_object(v___x_1979_);
lean_dec(v_a_1977_);
lean_del_object(v___x_1961_);
lean_dec(v_a_1959_);
lean_dec_ref(v_code_1946_);
v___x_2282_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4);
v___x_2283_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2282_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
return v___x_2283_;
}
case 14:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_del_object(v___x_1984_);
lean_dec(v_a_1982_);
lean_del_object(v___x_1979_);
lean_dec(v_a_1977_);
lean_del_object(v___x_1961_);
lean_dec(v_a_1959_);
lean_dec_ref(v_code_1946_);
v___x_2284_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4);
v___x_2285_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2284_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
return v___x_2285_;
}
case 15:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_del_object(v___x_1984_);
lean_dec(v_a_1982_);
lean_del_object(v___x_1979_);
lean_dec(v_a_1977_);
lean_del_object(v___x_1961_);
lean_dec(v_a_1959_);
lean_dec_ref(v_code_1946_);
v___x_2286_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4);
v___x_2287_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2286_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
return v___x_2287_;
}
default: 
{
lean_object* v___x_2288_; 
lean_inc(v_value_2006_);
lean_del_object(v___x_1984_);
lean_del_object(v___x_1961_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
v___x_2288_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_1963_, v_a_1977_, v_a_1959_, v_value_2006_, v_a_1952_);
lean_dec(v_a_1952_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2315_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2315_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2315_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
uint8_t v___y_2294_; 
if (lean_obj_tag(v_code_1946_) == 0)
{
lean_object* v_decl_2302_; lean_object* v_k_2303_; size_t v___x_2304_; size_t v___x_2305_; uint8_t v___x_2306_; 
lean_del_object(v___x_1979_);
v_decl_2302_ = lean_ctor_get(v_code_1946_, 0);
v_k_2303_ = lean_ctor_get(v_code_1946_, 1);
v___x_2304_ = lean_ptr_addr(v_k_2303_);
v___x_2305_ = lean_ptr_addr(v_a_1982_);
v___x_2306_ = lean_usize_dec_eq(v___x_2304_, v___x_2305_);
if (v___x_2306_ == 0)
{
v___y_2294_ = v___x_2306_;
goto v___jp_2293_;
}
else
{
size_t v___x_2307_; size_t v___x_2308_; uint8_t v___x_2309_; 
v___x_2307_ = lean_ptr_addr(v_decl_2302_);
v___x_2308_ = lean_ptr_addr(v_a_2289_);
v___x_2309_ = lean_usize_dec_eq(v___x_2307_, v___x_2308_);
v___y_2294_ = v___x_2309_;
goto v___jp_2293_;
}
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
lean_del_object(v___x_2291_);
lean_dec(v_a_2289_);
lean_dec(v_a_1982_);
lean_dec_ref(v_code_1946_);
v___x_2310_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2311_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2310_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_2311_);
v___x_2313_ = v___x_1979_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
v___jp_2293_:
{
if (v___y_2294_ == 0)
{
lean_object* v___x_2295_; lean_object* v___x_2297_; 
lean_dec_ref(v_code_1946_);
v___x_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2295_, 0, v_a_2289_);
lean_ctor_set(v___x_2295_, 1, v_a_1982_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2295_);
v___x_2297_ = v___x_2291_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
else
{
lean_object* v___x_2300_; 
lean_dec(v_a_2289_);
lean_dec(v_a_1982_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v_code_1946_);
v___x_2300_ = v___x_2291_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_code_1946_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec(v_a_1982_);
lean_del_object(v___x_1979_);
lean_dec_ref(v_code_1946_);
v_a_2316_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2288_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2288_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
v___jp_1986_:
{
if (v___y_1989_ == 0)
{
lean_object* v___x_1990_; 
lean_dec_ref(v_code_1946_);
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___y_1988_);
lean_ctor_set(v___x_1990_, 1, v_a_1982_);
v___y_1972_ = v___y_1987_;
v___y_1973_ = v___x_1990_;
goto v___jp_1971_;
}
else
{
lean_dec_ref(v___y_1988_);
lean_dec(v_a_1982_);
v___y_1972_ = v___y_1987_;
v___y_1973_ = v_code_1946_;
goto v___jp_1971_;
}
}
v___jp_1991_:
{
if (v___y_1993_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
lean_dec_ref(v_code_1946_);
v___x_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___y_1992_);
lean_ctor_set(v___x_1994_, 1, v_a_1982_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1994_);
v___x_1996_ = v___x_1984_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
else
{
lean_object* v___x_1999_; 
lean_dec_ref(v___y_1992_);
lean_dec(v_a_1982_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v_code_1946_);
v___x_1999_ = v___x_1984_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_code_1946_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
v___jp_2001_:
{
if (v___y_2004_ == 0)
{
lean_object* v___x_2005_; 
lean_dec_ref(v_code_1946_);
v___x_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___y_2002_);
lean_ctor_set(v___x_2005_, 1, v_a_1982_);
v___y_1965_ = v___y_2003_;
v___y_1966_ = v___x_2005_;
goto v___jp_1964_;
}
else
{
lean_dec_ref(v___y_2002_);
lean_dec(v_a_1982_);
v___y_1965_ = v___y_2003_;
v___y_1966_ = v_code_1946_;
goto v___jp_1964_;
}
}
}
}
else
{
lean_del_object(v___x_1979_);
lean_dec(v_a_1977_);
lean_del_object(v___x_1961_);
lean_dec(v_a_1959_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec_ref(v_code_1946_);
return v___x_1981_;
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_del_object(v___x_1961_);
lean_dec(v_a_1959_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec_ref(v_k_1948_);
lean_dec_ref(v_code_1946_);
v_a_2326_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_1976_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_1976_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
v___jp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1963_, v___y_1965_, v___y_1966_);
lean_dec_ref(v___y_1965_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1967_);
v___x_1969_ = v___x_1961_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
v___jp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1963_, v___y_1972_, v___y_1973_);
lean_dec_ref(v___y_1972_);
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
return v___x_1975_;
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_value_1957_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec_ref(v_k_1948_);
lean_dec_ref(v_decl_1947_);
lean_dec_ref(v_code_1946_);
v_a_2335_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_1958_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_1958_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2344_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_2345_ = lean_unsigned_to_nat(44u);
v___x_2346_ = lean_unsigned_to_nat(284u);
v___x_2347_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0));
v___x_2348_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
v___x_2349_ = l_mkPanicMessageWithDecl(v___x_2348_, v___x_2347_, v___x_2346_, v___x_2345_, v___x_2344_);
return v___x_2349_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2350_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_2351_ = lean_unsigned_to_nat(59u);
v___x_2352_ = lean_unsigned_to_nat(287u);
v___x_2353_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0));
v___x_2354_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
v___x_2355_ = l_mkPanicMessageWithDecl(v___x_2354_, v___x_2353_, v___x_2352_, v___x_2351_, v___x_2350_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(lean_object* v_code_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_){
_start:
{
switch(lean_obj_tag(v_code_2356_))
{
case 0:
{
lean_object* v_decl_2364_; lean_object* v_k_2365_; lean_object* v___x_2366_; 
v_decl_2364_ = lean_ctor_get(v_code_2356_, 0);
lean_inc_ref(v_decl_2364_);
v_k_2365_ = lean_ctor_get(v_code_2356_, 1);
lean_inc_ref(v_k_2365_);
v___x_2366_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(v_code_2356_, v_decl_2364_, v_k_2365_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
return v___x_2366_;
}
case 2:
{
lean_object* v_decl_2367_; lean_object* v_k_2368_; lean_object* v_params_2369_; lean_object* v_value_2370_; lean_object* v___x_2371_; 
v_decl_2367_ = lean_ctor_get(v_code_2356_, 0);
v_k_2368_ = lean_ctor_get(v_code_2356_, 1);
v_params_2369_ = lean_ctor_get(v_decl_2367_, 2);
v_value_2370_ = lean_ctor_get(v_decl_2367_, 4);
lean_inc(v_a_2362_);
lean_inc_ref(v_a_2361_);
lean_inc(v_a_2360_);
lean_inc_ref(v_a_2359_);
lean_inc(v_a_2358_);
lean_inc_ref(v_a_2357_);
lean_inc_ref(v_value_2370_);
v___x_2371_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_value_2370_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v_currDeclResultType_2373_; uint8_t v___x_2374_; lean_object* v___x_2375_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref(v___x_2371_);
v_currDeclResultType_2373_ = lean_ctor_get(v_a_2357_, 1);
v___x_2374_ = 1;
lean_inc_ref(v_params_2369_);
lean_inc_ref(v_currDeclResultType_2373_);
lean_inc_ref(v_decl_2367_);
v___x_2375_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2374_, v_decl_2367_, v_currDeclResultType_2373_, v_params_2369_, v_a_2372_, v_a_2360_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2377_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref(v___x_2375_);
lean_inc_ref(v_k_2368_);
v___x_2377_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2368_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2405_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2405_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2405_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
uint8_t v___y_2383_; size_t v___x_2399_; size_t v___x_2400_; uint8_t v___x_2401_; 
v___x_2399_ = lean_ptr_addr(v_k_2368_);
v___x_2400_ = lean_ptr_addr(v_a_2378_);
v___x_2401_ = lean_usize_dec_eq(v___x_2399_, v___x_2400_);
if (v___x_2401_ == 0)
{
v___y_2383_ = v___x_2401_;
goto v___jp_2382_;
}
else
{
size_t v___x_2402_; size_t v___x_2403_; uint8_t v___x_2404_; 
v___x_2402_ = lean_ptr_addr(v_decl_2367_);
v___x_2403_ = lean_ptr_addr(v_a_2376_);
v___x_2404_ = lean_usize_dec_eq(v___x_2402_, v___x_2403_);
v___y_2383_ = v___x_2404_;
goto v___jp_2382_;
}
v___jp_2382_:
{
if (v___y_2383_ == 0)
{
lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2393_; 
v_isSharedCheck_2393_ = !lean_is_exclusive(v_code_2356_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; lean_object* v_unused_2395_; 
v_unused_2394_ = lean_ctor_get(v_code_2356_, 1);
lean_dec(v_unused_2394_);
v_unused_2395_ = lean_ctor_get(v_code_2356_, 0);
lean_dec(v_unused_2395_);
v___x_2385_ = v_code_2356_;
v_isShared_2386_ = v_isSharedCheck_2393_;
goto v_resetjp_2384_;
}
else
{
lean_dec(v_code_2356_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2393_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 1, v_a_2378_);
lean_ctor_set(v___x_2385_, 0, v_a_2376_);
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2376_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_a_2378_);
v___x_2388_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2388_);
v___x_2390_ = v___x_2380_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_object* v___x_2397_; 
lean_dec(v_a_2378_);
lean_dec(v_a_2376_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v_code_2356_);
v___x_2397_ = v___x_2380_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_code_2356_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
else
{
lean_dec(v_a_2376_);
lean_dec_ref(v_code_2356_);
return v___x_2377_;
}
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec_ref(v_code_2356_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2406_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2375_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2375_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_dec_ref(v_code_2356_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
return v___x_2371_;
}
}
case 3:
{
lean_object* v_fvarId_2414_; lean_object* v_args_2415_; uint8_t v___x_2416_; lean_object* v___x_2417_; 
v_fvarId_2414_ = lean_ctor_get(v_code_2356_, 0);
v_args_2415_ = lean_ctor_get(v_code_2356_, 1);
v___x_2416_ = 1;
v___x_2417_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_2416_, v_fvarId_2414_, v_a_2360_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref(v___x_2417_);
if (lean_obj_tag(v_a_2418_) == 1)
{
lean_object* v_val_2419_; lean_object* v_params_2420_; lean_object* v___x_2421_; lean_object* v___f_2422_; lean_object* v___x_2423_; 
v_val_2419_ = lean_ctor_get(v_a_2418_, 0);
lean_inc(v_val_2419_);
lean_dec_ref(v_a_2418_);
v_params_2420_ = lean_ctor_get(v_val_2419_, 2);
lean_inc_ref(v_params_2420_);
lean_dec(v_val_2419_);
v___x_2421_ = lean_box(v___x_2416_);
v___f_2422_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2422_, 0, v___x_2421_);
lean_closure_set(v___f_2422_, 1, v_params_2420_);
v___x_2423_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2415_, v___f_2422_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2358_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2451_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2451_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2451_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_fst_2428_; lean_object* v_snd_2429_; lean_object* v___y_2431_; uint8_t v___y_2437_; uint8_t v___x_2447_; 
v_fst_2428_ = lean_ctor_get(v_a_2424_, 0);
lean_inc(v_fst_2428_);
v_snd_2429_ = lean_ctor_get(v_a_2424_, 1);
lean_inc(v_snd_2429_);
lean_dec(v_a_2424_);
v___x_2447_ = l_Lean_instBEqFVarId_beq(v_fvarId_2414_, v_fvarId_2414_);
if (v___x_2447_ == 0)
{
v___y_2437_ = v___x_2447_;
goto v___jp_2436_;
}
else
{
size_t v___x_2448_; size_t v___x_2449_; uint8_t v___x_2450_; 
v___x_2448_ = lean_ptr_addr(v_args_2415_);
v___x_2449_ = lean_ptr_addr(v_fst_2428_);
v___x_2450_ = lean_usize_dec_eq(v___x_2448_, v___x_2449_);
v___y_2437_ = v___x_2450_;
goto v___jp_2436_;
}
v___jp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2434_; 
v___x_2432_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2416_, v_snd_2429_, v___y_2431_);
lean_dec(v_snd_2429_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2432_);
v___x_2434_ = v___x_2426_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
v___jp_2436_:
{
if (v___y_2437_ == 0)
{
lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_inc(v_fvarId_2414_);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_code_2356_);
if (v_isSharedCheck_2444_ == 0)
{
lean_object* v_unused_2445_; lean_object* v_unused_2446_; 
v_unused_2445_ = lean_ctor_get(v_code_2356_, 1);
lean_dec(v_unused_2445_);
v_unused_2446_ = lean_ctor_get(v_code_2356_, 0);
lean_dec(v_unused_2446_);
v___x_2439_ = v_code_2356_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_dec(v_code_2356_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 1, v_fst_2428_);
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_fvarId_2414_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_fst_2428_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
v___y_2431_ = v___x_2442_;
goto v___jp_2430_;
}
}
}
else
{
lean_dec(v_fst_2428_);
v___y_2431_ = v_code_2356_;
goto v___jp_2430_;
}
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec_ref(v_code_2356_);
v_a_2452_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2423_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2423_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
else
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
lean_dec(v_a_2418_);
lean_dec_ref(v_code_2356_);
v___x_2460_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1);
v___x_2461_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2460_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
return v___x_2461_;
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v_code_2356_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2462_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2417_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2417_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
case 4:
{
lean_object* v_cases_2470_; lean_object* v_typeName_2471_; lean_object* v_resultType_2472_; lean_object* v_discr_2473_; lean_object* v_alts_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_cases_2470_ = lean_ctor_get(v_code_2356_, 0);
v_typeName_2471_ = lean_ctor_get(v_cases_2470_, 0);
lean_inc(v_typeName_2471_);
v_resultType_2472_ = lean_ctor_get(v_cases_2470_, 1);
lean_inc_ref(v_resultType_2472_);
v_discr_2473_ = lean_ctor_get(v_cases_2470_, 2);
lean_inc(v_discr_2473_);
v_alts_2474_ = lean_ctor_get(v_cases_2470_, 3);
lean_inc_ref(v_alts_2474_);
v___x_2475_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_2362_);
lean_inc_ref(v_a_2361_);
lean_inc(v_a_2360_);
lean_inc_ref(v_a_2359_);
lean_inc(v_a_2358_);
lean_inc_ref(v_a_2357_);
lean_inc_ref(v_alts_2474_);
v___x_2476_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(v___x_2475_, v_alts_2474_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2478_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref(v___x_2476_);
lean_inc(v_discr_2473_);
v___x_2478_ = l_Lean_Compiler_LCNF_getType(v_discr_2473_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref(v___x_2478_);
v___x_2480_ = lean_box(0);
lean_inc(v_typeName_2471_);
v___x_2481_ = l_Lean_mkConst(v_typeName_2471_, v___x_2480_);
v___x_2482_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2479_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; 
lean_inc(v_a_2362_);
lean_inc_ref(v_a_2361_);
lean_inc(v_a_2360_);
lean_inc_ref(v_a_2359_);
lean_inc_ref(v_a_2357_);
lean_inc_ref(v___x_2481_);
lean_inc(v_discr_2473_);
v___x_2483_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_discr_2473_, v_a_2479_, v___x_2481_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref(v___x_2483_);
v___x_2485_ = 1;
v___x_2486_ = lean_box(0);
v___x_2487_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2485_, v___x_2486_, v___x_2481_, v_a_2484_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v_fvarId_2489_; lean_object* v___x_2490_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref(v___x_2487_);
v_fvarId_2489_ = lean_ctor_get(v_a_2488_, 0);
lean_inc(v_fvarId_2489_);
v___x_2490_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_2471_, v_a_2477_, v_discr_2473_, v_code_2356_, v_alts_2474_, v_resultType_2472_, v_fvarId_2489_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec_ref(v_resultType_2472_);
lean_dec_ref(v_alts_2474_);
lean_dec(v_discr_2473_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2499_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2499_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2499_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v_a_2488_);
lean_ctor_set(v___x_2495_, 1, v_a_2491_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2495_);
v___x_2497_ = v___x_2493_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
else
{
lean_dec(v_a_2488_);
return v___x_2490_;
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_a_2477_);
lean_dec_ref(v_alts_2474_);
lean_dec(v_discr_2473_);
lean_dec_ref(v_resultType_2472_);
lean_dec(v_typeName_2471_);
lean_dec_ref(v_code_2356_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2500_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2487_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2487_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec_ref(v___x_2481_);
lean_dec(v_a_2477_);
lean_dec_ref(v_alts_2474_);
lean_dec(v_discr_2473_);
lean_dec_ref(v_resultType_2472_);
lean_dec(v_typeName_2471_);
lean_dec_ref(v_code_2356_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2508_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2483_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2483_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_object* v___x_2516_; 
lean_dec_ref(v___x_2481_);
lean_dec(v_a_2479_);
lean_inc(v_discr_2473_);
v___x_2516_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_2471_, v_a_2477_, v_discr_2473_, v_code_2356_, v_alts_2474_, v_resultType_2472_, v_discr_2473_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec_ref(v_resultType_2472_);
lean_dec_ref(v_alts_2474_);
lean_dec(v_discr_2473_);
return v___x_2516_;
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec(v_a_2477_);
lean_dec_ref(v_alts_2474_);
lean_dec(v_discr_2473_);
lean_dec_ref(v_resultType_2472_);
lean_dec(v_typeName_2471_);
lean_dec_ref(v_code_2356_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2517_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2478_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2478_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec_ref(v_alts_2474_);
lean_dec(v_discr_2473_);
lean_dec_ref(v_resultType_2472_);
lean_dec(v_typeName_2471_);
lean_dec_ref(v_code_2356_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2525_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2476_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2476_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_2533_; lean_object* v___x_2534_; 
v_fvarId_2533_ = lean_ctor_get(v_code_2356_, 0);
lean_inc(v_fvarId_2533_);
lean_inc(v_fvarId_2533_);
v___x_2534_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2533_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v_currDeclResultType_2536_; uint8_t v___x_2537_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref(v___x_2534_);
v_currDeclResultType_2536_ = lean_ctor_get(v_a_2357_, 1);
v___x_2537_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2535_, v_currDeclResultType_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; 
lean_inc(v_a_2362_);
lean_inc_ref(v_a_2361_);
lean_inc(v_a_2360_);
lean_inc_ref(v_a_2359_);
lean_inc_ref(v_a_2357_);
lean_inc_ref(v_currDeclResultType_2536_);
lean_inc(v_fvarId_2533_);
v___x_2538_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_2533_, v_a_2535_, v_currDeclResultType_2536_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; uint8_t v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref(v___x_2538_);
v___x_2540_ = 1;
v___x_2541_ = lean_box(0);
lean_inc_ref(v_currDeclResultType_2536_);
v___x_2542_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2540_, v___x_2541_, v_currDeclResultType_2536_, v_a_2539_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v_fvarId_2544_; lean_object* v___x_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2560_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref(v___x_2542_);
v_fvarId_2544_ = lean_ctor_get(v_a_2543_, 0);
lean_inc(v_fvarId_2544_);
v___x_2545_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_2533_, v_code_2356_, v_fvarId_2544_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec(v_fvarId_2533_);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_a_2357_);
if (v_isSharedCheck_2560_ == 0)
{
lean_object* v_unused_2561_; lean_object* v_unused_2562_; 
v_unused_2561_ = lean_ctor_get(v_a_2357_, 1);
lean_dec(v_unused_2561_);
v_unused_2562_ = lean_ctor_get(v_a_2357_, 0);
lean_dec(v_unused_2562_);
v___x_2547_ = v_a_2357_;
v_isShared_2548_ = v_isSharedCheck_2560_;
goto v_resetjp_2546_;
}
else
{
lean_dec(v_a_2357_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2560_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2559_; 
v_a_2549_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2551_ = v___x_2545_;
v_isShared_2552_ = v_isSharedCheck_2559_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2545_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2559_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 1, v_a_2549_);
lean_ctor_set(v___x_2547_, 0, v_a_2543_);
v___x_2554_ = v___x_2547_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2543_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2556_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v___x_2554_);
v___x_2556_ = v___x_2551_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
else
{
lean_del_object(v___x_2547_);
lean_dec(v_a_2543_);
return v___x_2545_;
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref(v_code_2356_);
lean_dec(v_fvarId_2533_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2563_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2542_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2542_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec_ref(v_code_2356_);
lean_dec(v_fvarId_2533_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2571_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2538_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2538_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
else
{
lean_object* v___x_2579_; 
lean_dec(v_a_2535_);
lean_inc(v_fvarId_2533_);
v___x_2579_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_2533_, v_code_2356_, v_fvarId_2533_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_fvarId_2533_);
return v___x_2579_;
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec_ref(v_code_2356_);
lean_dec(v_fvarId_2533_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2580_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2534_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2534_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
case 6:
{
lean_object* v_type_2588_; lean_object* v_currDeclResultType_2589_; size_t v___x_2590_; size_t v___x_2591_; uint8_t v___x_2592_; 
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
v_type_2588_ = lean_ctor_get(v_code_2356_, 0);
v_currDeclResultType_2589_ = lean_ctor_get(v_a_2357_, 1);
lean_inc_ref(v_currDeclResultType_2589_);
lean_dec_ref(v_a_2357_);
v___x_2590_ = lean_ptr_addr(v_type_2588_);
v___x_2591_ = lean_ptr_addr(v_currDeclResultType_2589_);
v___x_2592_ = lean_usize_dec_eq(v___x_2590_, v___x_2591_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2600_; 
v_isSharedCheck_2600_ = !lean_is_exclusive(v_code_2356_);
if (v_isSharedCheck_2600_ == 0)
{
lean_object* v_unused_2601_; 
v_unused_2601_ = lean_ctor_get(v_code_2356_, 0);
lean_dec(v_unused_2601_);
v___x_2594_ = v_code_2356_;
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
else
{
lean_dec(v_code_2356_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v_currDeclResultType_2589_);
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_currDeclResultType_2589_);
v___x_2597_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2598_; 
v___x_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
return v___x_2598_;
}
}
}
else
{
lean_object* v___x_2602_; 
lean_dec_ref(v_currDeclResultType_2589_);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v_code_2356_);
return v___x_2602_;
}
}
case 8:
{
lean_object* v_fvarId_2603_; lean_object* v_i_2604_; lean_object* v_y_2605_; lean_object* v_k_2606_; lean_object* v___x_2607_; 
v_fvarId_2603_ = lean_ctor_get(v_code_2356_, 0);
lean_inc(v_fvarId_2603_);
v_i_2604_ = lean_ctor_get(v_code_2356_, 1);
lean_inc(v_i_2604_);
v_y_2605_ = lean_ctor_get(v_code_2356_, 2);
lean_inc(v_y_2605_);
v_k_2606_ = lean_ctor_get(v_code_2356_, 3);
lean_inc_ref(v_k_2606_);
lean_inc(v_a_2362_);
lean_inc_ref(v_a_2361_);
lean_inc(v_a_2360_);
lean_inc_ref(v_a_2359_);
lean_inc(v_a_2358_);
lean_inc_ref(v_a_2357_);
lean_inc_ref(v_k_2606_);
v___x_2607_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2606_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2609_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref(v___x_2607_);
lean_inc(v_y_2605_);
v___x_2609_ = l_Lean_Compiler_LCNF_getType(v_y_2605_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref(v___x_2609_);
v___x_2611_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
v___x_2612_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2610_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; 
lean_inc(v_a_2362_);
lean_inc_ref(v_a_2361_);
lean_inc(v_a_2360_);
lean_inc_ref(v_a_2359_);
lean_inc_ref(v_a_2357_);
lean_inc(v_y_2605_);
v___x_2613_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_y_2605_, v_a_2610_, v___x_2611_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; uint8_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref(v___x_2613_);
v___x_2615_ = 1;
v___x_2616_ = lean_box(0);
v___x_2617_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2615_, v___x_2616_, v___x_2611_, v_a_2614_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v_fvarId_2619_; lean_object* v___x_2620_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref(v___x_2617_);
v_fvarId_2619_ = lean_ctor_get(v_a_2618_, 0);
lean_inc(v_fvarId_2619_);
v___x_2620_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_2603_, v_i_2604_, v_a_2608_, v_y_2605_, v_k_2606_, v_code_2356_, v_fvarId_2619_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec_ref(v_k_2606_);
lean_dec(v_y_2605_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2629_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2629_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2629_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v_a_2618_);
lean_ctor_set(v___x_2625_, 1, v_a_2621_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2625_);
v___x_2627_ = v___x_2623_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
else
{
lean_dec(v_a_2618_);
return v___x_2620_;
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_a_2608_);
lean_dec_ref(v_k_2606_);
lean_dec(v_y_2605_);
lean_dec(v_i_2604_);
lean_dec(v_fvarId_2603_);
lean_dec_ref(v_code_2356_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2630_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2617_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2617_);
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
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_a_2608_);
lean_dec_ref(v_k_2606_);
lean_dec(v_y_2605_);
lean_dec(v_i_2604_);
lean_dec(v_fvarId_2603_);
lean_dec_ref(v_code_2356_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2638_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2613_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2613_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v___x_2646_; 
lean_dec(v_a_2610_);
lean_inc(v_y_2605_);
v___x_2646_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_2603_, v_i_2604_, v_a_2608_, v_y_2605_, v_k_2606_, v_code_2356_, v_y_2605_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec_ref(v_k_2606_);
lean_dec(v_y_2605_);
return v___x_2646_;
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec(v_a_2608_);
lean_dec_ref(v_k_2606_);
lean_dec(v_y_2605_);
lean_dec(v_i_2604_);
lean_dec(v_fvarId_2603_);
lean_dec_ref(v_code_2356_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2647_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2609_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2609_);
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
else
{
lean_dec_ref(v_k_2606_);
lean_dec(v_y_2605_);
lean_dec(v_i_2604_);
lean_dec(v_fvarId_2603_);
lean_dec_ref(v_code_2356_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
return v___x_2607_;
}
}
case 9:
{
lean_object* v_fvarId_2655_; lean_object* v_i_2656_; lean_object* v_offset_2657_; lean_object* v_y_2658_; lean_object* v_ty_2659_; lean_object* v_k_2660_; lean_object* v___x_2661_; 
v_fvarId_2655_ = lean_ctor_get(v_code_2356_, 0);
lean_inc(v_fvarId_2655_);
v_i_2656_ = lean_ctor_get(v_code_2356_, 1);
lean_inc(v_i_2656_);
v_offset_2657_ = lean_ctor_get(v_code_2356_, 2);
lean_inc(v_offset_2657_);
v_y_2658_ = lean_ctor_get(v_code_2356_, 3);
lean_inc(v_y_2658_);
v_ty_2659_ = lean_ctor_get(v_code_2356_, 4);
lean_inc_ref(v_ty_2659_);
v_k_2660_ = lean_ctor_get(v_code_2356_, 5);
lean_inc_ref(v_k_2660_);
lean_inc(v_a_2362_);
lean_inc_ref(v_a_2361_);
lean_inc(v_a_2360_);
lean_inc_ref(v_a_2359_);
lean_inc(v_a_2358_);
lean_inc_ref(v_a_2357_);
lean_inc_ref(v_k_2660_);
v___x_2661_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2660_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2663_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref(v___x_2661_);
lean_inc(v_y_2658_);
v___x_2663_ = l_Lean_Compiler_LCNF_getType(v_y_2658_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; uint8_t v___x_2665_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref(v___x_2663_);
v___x_2665_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2664_, v_ty_2659_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; 
lean_inc(v_a_2362_);
lean_inc_ref(v_a_2361_);
lean_inc(v_a_2360_);
lean_inc_ref(v_a_2359_);
lean_inc_ref(v_a_2357_);
lean_inc_ref(v_ty_2659_);
lean_inc(v_y_2658_);
v___x_2666_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_y_2658_, v_a_2664_, v_ty_2659_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref(v___x_2666_);
v___x_2668_ = 1;
v___x_2669_ = lean_box(0);
lean_inc_ref(v_ty_2659_);
v___x_2670_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2668_, v___x_2669_, v_ty_2659_, v_a_2667_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v_fvarId_2672_; lean_object* v___x_2673_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref(v___x_2670_);
v_fvarId_2672_ = lean_ctor_get(v_a_2671_, 0);
lean_inc(v_fvarId_2672_);
v___x_2673_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_2655_, v_i_2656_, v_offset_2657_, v_ty_2659_, v_a_2662_, v_y_2658_, v_k_2660_, v_code_2356_, v_fvarId_2672_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec_ref(v_k_2660_);
lean_dec(v_y_2658_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2682_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2676_ = v___x_2673_;
v_isShared_2677_ = v_isSharedCheck_2682_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2673_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2682_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2678_, 0, v_a_2671_);
lean_ctor_set(v___x_2678_, 1, v_a_2674_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2678_);
v___x_2680_ = v___x_2676_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
else
{
lean_dec(v_a_2671_);
return v___x_2673_;
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec(v_a_2662_);
lean_dec_ref(v_k_2660_);
lean_dec_ref(v_ty_2659_);
lean_dec(v_y_2658_);
lean_dec(v_offset_2657_);
lean_dec(v_i_2656_);
lean_dec_ref(v_code_2356_);
lean_dec(v_fvarId_2655_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2683_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2670_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2670_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_a_2662_);
lean_dec_ref(v_k_2660_);
lean_dec_ref(v_ty_2659_);
lean_dec(v_y_2658_);
lean_dec(v_offset_2657_);
lean_dec(v_i_2656_);
lean_dec_ref(v_code_2356_);
lean_dec(v_fvarId_2655_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2691_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2666_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2666_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
else
{
lean_object* v___x_2699_; 
lean_dec(v_a_2664_);
lean_inc(v_y_2658_);
v___x_2699_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_2655_, v_i_2656_, v_offset_2657_, v_ty_2659_, v_a_2662_, v_y_2658_, v_k_2660_, v_code_2356_, v_y_2658_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec_ref(v_k_2660_);
lean_dec(v_y_2658_);
return v___x_2699_;
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v_a_2662_);
lean_dec_ref(v_k_2660_);
lean_dec_ref(v_ty_2659_);
lean_dec(v_y_2658_);
lean_dec(v_offset_2657_);
lean_dec(v_i_2656_);
lean_dec_ref(v_code_2356_);
lean_dec(v_fvarId_2655_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
v_a_2700_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2663_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2663_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
else
{
lean_dec_ref(v_k_2660_);
lean_dec_ref(v_ty_2659_);
lean_dec(v_y_2658_);
lean_dec(v_offset_2657_);
lean_dec(v_i_2656_);
lean_dec_ref(v_code_2356_);
lean_dec(v_fvarId_2655_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
return v___x_2661_;
}
}
default: 
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_dec_ref(v_code_2356_);
v___x_2708_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2);
v___x_2709_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2708_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
return v___x_2709_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed(lean_object* v_code_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_code_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(lean_object* v_i_2719_, lean_object* v_as_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2728_ = lean_array_get_size(v_as_2720_);
v___x_2729_ = lean_nat_dec_lt(v_i_2719_, v___x_2728_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; 
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v_i_2719_);
v___x_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_as_2720_);
return v___x_2730_;
}
else
{
lean_object* v___f_2731_; lean_object* v_a_2732_; lean_object* v___x_2733_; 
v___f_2731_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed), 8, 0);
v_a_2732_ = lean_array_fget_borrowed(v_as_2720_, v_i_2719_);
lean_inc(v___y_2726_);
lean_inc_ref(v___y_2725_);
lean_inc(v___y_2724_);
lean_inc_ref(v___y_2723_);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
lean_inc(v_a_2732_);
v___x_2733_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_a_2732_, v___f_2731_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; size_t v___x_2735_; size_t v___x_2736_; uint8_t v___x_2737_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref(v___x_2733_);
v___x_2735_ = lean_ptr_addr(v_a_2732_);
v___x_2736_ = lean_ptr_addr(v_a_2734_);
v___x_2737_ = lean_usize_dec_eq(v___x_2735_, v___x_2736_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2738_ = lean_unsigned_to_nat(1u);
v___x_2739_ = lean_nat_add(v_i_2719_, v___x_2738_);
v___x_2740_ = lean_array_fset(v_as_2720_, v_i_2719_, v_a_2734_);
lean_dec(v_i_2719_);
v_i_2719_ = v___x_2739_;
v_as_2720_ = v___x_2740_;
goto _start;
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
lean_dec(v_a_2734_);
v___x_2742_ = lean_unsigned_to_nat(1u);
v___x_2743_ = lean_nat_add(v_i_2719_, v___x_2742_);
lean_dec(v_i_2719_);
v_i_2719_ = v___x_2743_;
goto _start;
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec_ref(v_as_2720_);
lean_dec(v_i_2719_);
v_a_2745_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2733_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2733_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3___boxed(lean_object* v_i_2753_, lean_object* v_as_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(v_i_2753_, v_as_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___boxed(lean_object* v_code_2763_, lean_object* v_decl_2764_, lean_object* v_k_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(v_code_2763_, v_decl_2764_, v_k_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(uint8_t v_pu_2774_, lean_object* v_alt_2775_, lean_object* v_f_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_alt_2775_, v_f_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___boxed(lean_object* v_pu_2785_, lean_object* v_alt_2786_, lean_object* v_f_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
uint8_t v_pu_boxed_2795_; lean_object* v_res_2796_; 
v_pu_boxed_2795_ = lean_unbox(v_pu_2785_);
v_res_2796_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(v_pu_boxed_2795_, v_alt_2786_, v_f_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(lean_object* v_as_2800_, size_t v_i_2801_, size_t v_stop_2802_, lean_object* v_b_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_a_2810_; uint8_t v___x_2814_; 
v___x_2814_ = lean_usize_dec_eq(v_i_2801_, v_stop_2802_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2815_; lean_object* v_value_2816_; 
v___x_2815_ = lean_array_uget(v_as_2800_, v_i_2801_);
v_value_2816_ = lean_ctor_get(v___x_2815_, 1);
lean_inc_ref(v_value_2816_);
if (lean_obj_tag(v_value_2816_) == 0)
{
lean_object* v_toSignature_2817_; uint8_t v_recursive_2818_; lean_object* v_inlineAttr_x3f_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2864_; 
v_toSignature_2817_ = lean_ctor_get(v___x_2815_, 0);
v_recursive_2818_ = lean_ctor_get_uint8(v___x_2815_, sizeof(void*)*3);
v_inlineAttr_x3f_2819_ = lean_ctor_get(v___x_2815_, 2);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2864_ == 0)
{
lean_object* v_unused_2865_; 
v_unused_2865_ = lean_ctor_get(v___x_2815_, 1);
lean_dec(v_unused_2865_);
v___x_2821_ = v___x_2815_;
v_isShared_2822_ = v_isSharedCheck_2864_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_inlineAttr_x3f_2819_);
lean_inc(v_toSignature_2817_);
lean_dec(v___x_2815_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2864_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v_code_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2863_; 
v_code_2823_ = lean_ctor_get(v_value_2816_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v_value_2816_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2825_ = v_value_2816_;
v_isShared_2826_ = v_isSharedCheck_2863_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_code_2823_);
lean_dec(v_value_2816_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2863_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v_name_2829_; lean_object* v_type_2830_; lean_object* v_s_2831_; lean_object* v___x_2832_; 
v___x_2827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0));
v___x_2828_ = lean_st_mk_ref(v___x_2827_);
v_name_2829_ = lean_ctor_get(v_toSignature_2817_, 0);
v_type_2830_ = lean_ctor_get(v_toSignature_2817_, 2);
lean_inc_ref(v_type_2830_);
lean_inc(v_name_2829_);
v_s_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_2831_, 0, v_name_2829_);
lean_ctor_set(v_s_2831_, 1, v_type_2830_);
lean_inc(v___y_2807_);
lean_inc_ref(v___y_2806_);
lean_inc(v___y_2805_);
lean_inc_ref(v___y_2804_);
lean_inc(v___x_2828_);
v___x_2832_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_code_2823_, v_s_2831_, v___x_2828_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; lean_object* v___x_2837_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref(v___x_2832_);
v___x_2834_ = lean_st_ref_get(v___x_2828_);
lean_dec(v___x_2828_);
v___x_2835_ = 1;
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v_a_2833_);
v___x_2837_ = v___x_2825_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2833_);
v___x_2837_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2839_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 1, v___x_2837_);
v___x_2839_ = v___x_2821_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_toSignature_2817_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_inlineAttr_x3f_2819_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, sizeof(void*)*3, v_recursive_2818_);
v___x_2839_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2840_; 
lean_inc(v___y_2807_);
lean_inc_ref(v___y_2806_);
lean_inc(v___y_2805_);
lean_inc_ref(v___y_2804_);
v___x_2840_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_2835_, v___x_2839_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v_auxDecls_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2841_);
lean_dec_ref(v___x_2840_);
v_auxDecls_2842_ = lean_ctor_get(v___x_2834_, 0);
lean_inc_ref(v_auxDecls_2842_);
lean_dec(v___x_2834_);
v___x_2843_ = l_Array_append___redArg(v_b_2803_, v_auxDecls_2842_);
lean_dec_ref(v_auxDecls_2842_);
v___x_2844_ = lean_array_push(v___x_2843_, v_a_2841_);
v_a_2810_ = v___x_2844_;
goto v___jp_2809_;
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec(v___x_2834_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec_ref(v_b_2803_);
v_a_2845_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2840_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2840_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v___x_2828_);
lean_del_object(v___x_2825_);
lean_del_object(v___x_2821_);
lean_dec(v_inlineAttr_x3f_2819_);
lean_dec_ref(v_toSignature_2817_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec_ref(v_b_2803_);
v_a_2855_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2832_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2832_);
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
else
{
lean_object* v___x_2866_; 
lean_dec_ref(v_value_2816_);
v___x_2866_ = lean_array_push(v_b_2803_, v___x_2815_);
v_a_2810_ = v___x_2866_;
goto v___jp_2809_;
}
}
else
{
lean_object* v___x_2867_; 
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v_b_2803_);
return v___x_2867_;
}
v___jp_2809_:
{
size_t v___x_2811_; size_t v___x_2812_; 
v___x_2811_ = ((size_t)1ULL);
v___x_2812_ = lean_usize_add(v_i_2801_, v___x_2811_);
v_i_2801_ = v___x_2812_;
v_b_2803_ = v_a_2810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___boxed(lean_object* v_as_2868_, lean_object* v_i_2869_, lean_object* v_stop_2870_, lean_object* v_b_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
size_t v_i_boxed_2877_; size_t v_stop_boxed_2878_; lean_object* v_res_2879_; 
v_i_boxed_2877_ = lean_unbox_usize(v_i_2869_);
lean_dec(v_i_2869_);
v_stop_boxed_2878_ = lean_unbox_usize(v_stop_2870_);
lean_dec(v_stop_2870_);
v_res_2879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_as_2868_, v_i_boxed_2877_, v_stop_boxed_2878_, v_b_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec_ref(v_as_2868_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(lean_object* v_decls_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v___y_2887_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; uint8_t v___x_2893_; 
v___x_2890_ = lean_unsigned_to_nat(0u);
v___x_2891_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0));
v___x_2892_ = lean_array_get_size(v_decls_2880_);
v___x_2893_ = lean_nat_dec_lt(v___x_2890_, v___x_2892_);
if (v___x_2893_ == 0)
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_Compiler_LCNF_addBoxedVersions(v___x_2891_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
return v___x_2894_;
}
else
{
uint8_t v___x_2895_; 
v___x_2895_ = lean_nat_dec_le(v___x_2892_, v___x_2892_);
if (v___x_2895_ == 0)
{
if (v___x_2893_ == 0)
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_Compiler_LCNF_addBoxedVersions(v___x_2891_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
return v___x_2896_;
}
else
{
size_t v___x_2897_; size_t v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = ((size_t)0ULL);
v___x_2898_ = lean_usize_of_nat(v___x_2892_);
lean_inc(v_a_2884_);
lean_inc_ref(v_a_2883_);
lean_inc(v_a_2882_);
lean_inc_ref(v_a_2881_);
v___x_2899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_decls_2880_, v___x_2897_, v___x_2898_, v___x_2891_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_);
v___y_2887_ = v___x_2899_;
goto v___jp_2886_;
}
}
else
{
size_t v___x_2900_; size_t v___x_2901_; lean_object* v___x_2902_; 
v___x_2900_ = ((size_t)0ULL);
v___x_2901_ = lean_usize_of_nat(v___x_2892_);
lean_inc(v_a_2884_);
lean_inc_ref(v_a_2883_);
lean_inc(v_a_2882_);
lean_inc_ref(v_a_2881_);
v___x_2902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_decls_2880_, v___x_2900_, v___x_2901_, v___x_2891_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_);
v___y_2887_ = v___x_2902_;
goto v___jp_2886_;
}
}
v___jp_2886_:
{
if (lean_obj_tag(v___y_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2889_; 
v_a_2888_ = lean_ctor_get(v___y_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref(v___y_2887_);
v___x_2889_ = l_Lean_Compiler_LCNF_addBoxedVersions(v_a_2888_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
return v___x_2889_;
}
else
{
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
return v___y_2887_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run___boxed(lean_object* v_decls_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(v_decls_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
lean_dec_ref(v_decls_2903_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2991_; uint8_t v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2991_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_));
v___x_2992_ = 1;
v___x_2993_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_));
v___x_2994_ = l_Lean_registerTraceClass(v___x_2991_, v___x_2992_, v___x_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2____boxed(lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_();
return v_res_2996_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_AuxDeclCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Runtime(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Runtime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ExplicitBoxing(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_AuxDeclCache(uint8_t builtin);
lean_object* initialize_Lean_Runtime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ExplicitBoxing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ElimDead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Runtime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
}
#ifdef __cplusplus
}
#endif
