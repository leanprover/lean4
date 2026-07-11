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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Compiler.LCNF.ExplicitBoxing"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 106, .m_capacity = 106, .m_length = 105, .m_data = "_private.Lean.Compiler.LCNF.ExplicitBoxing.0.Lean.Compiler.LCNF.Code.explicitBoxing.tryCorrectLetDeclType"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tagged"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 57, 252, 162, 142, 133, 51, 193)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "obj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__6_value),LEAN_SCALAR_PTR_LITERAL(240, 235, 44, 74, 242, 121, 239, 90)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
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
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "_private.Lean.Compiler.LCNF.ExplicitBoxing.0.Lean.Compiler.LCNF.Code.explicitBoxing.visitLet"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2_value;
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
lean_dec_ref_known(v___x_88_, 1);
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
lean_object* v_snd_132_; lean_object* v_snd_133_; lean_object* v_fst_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_208_; 
v_snd_132_ = lean_ctor_get(v_b_119_, 1);
lean_inc(v_snd_132_);
v_snd_133_ = lean_ctor_get(v_snd_132_, 1);
lean_inc(v_snd_133_);
v_fst_134_ = lean_ctor_get(v_b_119_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v_b_119_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; 
v_unused_209_ = lean_ctor_get(v_b_119_, 1);
lean_dec(v_unused_209_);
v___x_136_ = v_b_119_;
v_isShared_137_ = v_isSharedCheck_208_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_fst_134_);
lean_dec(v_b_119_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_208_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_fst_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_206_; 
v_fst_138_ = lean_ctor_get(v_snd_132_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v_snd_132_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v_snd_132_, 1);
lean_dec(v_unused_207_);
v___x_140_ = v_snd_132_;
v_isShared_141_ = v_isSharedCheck_206_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_fst_138_);
lean_dec(v_snd_132_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_206_;
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
lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_202_; 
lean_inc(v_stop_144_);
lean_inc(v_start_143_);
lean_inc_ref(v_array_142_);
v_isSharedCheck_202_ = !lean_is_exclusive(v_snd_133_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; lean_object* v_unused_204_; lean_object* v_unused_205_; 
v_unused_203_ = lean_ctor_get(v_snd_133_, 2);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_snd_133_, 1);
lean_dec(v_unused_204_);
v_unused_205_ = lean_ctor_get(v_snd_133_, 0);
lean_dec(v_unused_205_);
v___x_154_ = v_snd_133_;
v_isShared_155_ = v_isSharedCheck_202_;
goto v_resetjp_153_;
}
else
{
lean_dec(v_snd_133_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_202_;
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
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_array_142_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_stop_144_);
v___x_163_ = v_reuseFailAlloc_201_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
uint8_t v___x_164_; uint8_t v___x_165_; 
v___x_164_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_158_);
v___x_165_ = lean_bool_not(v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v_fvarId_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_fvarId_166_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_fvarId_166_);
lean_dec(v___x_159_);
v___x_167_ = 1;
v___x_168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0));
lean_inc(v_binderName_157_);
v___x_169_ = l_Lean_Name_str___override(v_binderName_157_, v___x_168_);
v___x_170_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_170_, 0, v_fvarId_166_);
lean_inc_ref(v_type_158_);
v___x_171_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_167_, v___x_169_, v_type_158_, v___x_170_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v_fvarId_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v___x_171_, 1);
v_fvarId_173_ = lean_ctor_get(v_a_172_, 0);
lean_inc(v_fvarId_173_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v_a_172_);
v___x_175_ = lean_array_push(v_fst_134_, v___x_174_);
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v_fvarId_173_);
v___x_177_ = lean_array_push(v_fst_138_, v___x_176_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_163_);
lean_ctor_set(v___x_140_, 0, v___x_177_);
v___x_179_ = v___x_140_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_163_);
v___x_179_ = v_reuseFailAlloc_183_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_181_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_179_);
lean_ctor_set(v___x_136_, 0, v___x_175_);
v___x_181_ = v___x_136_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
v_a_126_ = v___x_181_;
goto v___jp_125_;
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_dec_ref(v___x_163_);
lean_del_object(v___x_140_);
lean_dec(v_fst_138_);
lean_del_object(v___x_136_);
lean_dec(v_fst_134_);
v_a_184_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_171_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_171_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
else
{
lean_object* v_fvarId_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v_fvarId_192_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_fvarId_192_);
lean_dec(v___x_159_);
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v_fvarId_192_);
v___x_194_ = lean_array_push(v_fst_138_, v___x_193_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_163_);
lean_ctor_set(v___x_140_, 0, v___x_194_);
v___x_196_ = v___x_140_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___x_163_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_196_);
v___x_198_ = v___x_136_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_fst_134_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
v_a_126_ = v___x_198_;
goto v___jp_125_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___boxed(lean_object* v_as_210_, lean_object* v_sz_211_, lean_object* v_i_212_, lean_object* v_b_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
size_t v_sz_boxed_219_; size_t v_i_boxed_220_; lean_object* v_res_221_; 
v_sz_boxed_219_ = lean_unbox_usize(v_sz_211_);
lean_dec(v_sz_211_);
v_i_boxed_220_ = lean_unbox_usize(v_i_212_);
lean_dec(v_i_212_);
v_res_221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(v_as_210_, v_sz_boxed_219_, v_i_boxed_220_, v_b_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec_ref(v_as_210_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(lean_object* v_sig_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_name_236_; lean_object* v_type_237_; lean_object* v_params_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_358_; 
v_name_236_ = lean_ctor_get(v_sig_230_, 0);
v_type_237_ = lean_ctor_get(v_sig_230_, 2);
v_params_238_ = lean_ctor_get(v_sig_230_, 3);
v_isSharedCheck_358_ = !lean_is_exclusive(v_sig_230_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v_sig_230_, 1);
lean_dec(v_unused_359_);
v___x_240_ = v_sig_230_;
v_isShared_241_ = v_isSharedCheck_358_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_params_238_);
lean_inc(v_type_237_);
lean_inc(v_name_236_);
lean_dec(v_sig_230_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_358_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
size_t v_sz_242_; size_t v___x_243_; lean_object* v___x_244_; 
v_sz_242_ = lean_array_size(v_params_238_);
v___x_243_ = ((size_t)0ULL);
lean_inc_ref(v_params_238_);
v___x_244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(v_sz_242_, v___x_243_, v_params_238_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v_value_247_; lean_object* v___y_248_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc_n(v_a_245_, 2);
lean_dec_ref_known(v___x_244_, 1);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0));
v___x_279_ = lean_array_get_size(v_params_238_);
v___x_280_ = lean_mk_empty_array_with_capacity(v___x_279_);
v___x_281_ = lean_array_get_size(v_a_245_);
v___x_282_ = l_Array_toSubarray___redArg(v_a_245_, v___x_277_, v___x_281_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_280_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_278_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(v_params_238_, v_sz_242_, v___x_243_, v___x_284_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
lean_dec_ref(v_params_238_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v_snd_287_; lean_object* v_fst_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_341_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_285_, 1);
v_snd_287_ = lean_ctor_get(v_a_286_, 1);
v_fst_288_ = lean_ctor_get(v_a_286_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v_a_286_);
if (v_isSharedCheck_341_ == 0)
{
v___x_290_ = v_a_286_;
v_isShared_291_ = v_isSharedCheck_341_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_snd_287_);
lean_inc(v_fst_288_);
lean_dec(v_a_286_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_341_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_fst_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_339_; 
v_fst_292_ = lean_ctor_get(v_snd_287_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v_snd_287_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; 
v_unused_340_ = lean_ctor_get(v_snd_287_, 1);
lean_dec(v_unused_340_);
v___x_294_ = v_snd_287_;
v_isShared_295_ = v_isSharedCheck_339_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_fst_292_);
lean_dec(v_snd_287_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_339_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_296_ = 1;
v___x_297_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2));
lean_inc(v_name_236_);
if (v_isShared_295_ == 0)
{
lean_ctor_set_tag(v___x_294_, 9);
lean_ctor_set(v___x_294_, 1, v_fst_292_);
lean_ctor_set(v___x_294_, 0, v_name_236_);
v___x_299_ = v___x_294_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_name_236_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_fst_292_);
v___x_299_ = v_reuseFailAlloc_338_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; 
lean_inc_ref(v_type_237_);
v___x_300_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_296_, v___x_297_, v_type_237_, v___x_299_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; uint8_t v___x_305_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc_n(v_a_301_, 2);
lean_dec_ref_known(v___x_300_, 1);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v_a_301_);
v___x_303_ = lean_array_push(v_fst_288_, v___x_302_);
v___x_304_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_237_);
v___x_305_ = lean_bool_not(v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v_fvarId_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v_fvarId_306_ = lean_ctor_get(v_a_301_, 0);
lean_inc(v_fvarId_306_);
lean_dec(v_a_301_);
v___x_307_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4));
v___x_308_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_237_);
lean_inc_ref(v_type_237_);
if (v_isShared_291_ == 0)
{
lean_ctor_set_tag(v___x_290_, 13);
lean_ctor_set(v___x_290_, 1, v_fvarId_306_);
lean_ctor_set(v___x_290_, 0, v_type_237_);
v___x_310_ = v___x_290_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_type_237_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_fvarId_306_);
v___x_310_ = v_reuseFailAlloc_326_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_296_, v___x_307_, v___x_308_, v___x_310_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v_fvarId_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_311_, 1);
v_fvarId_313_ = lean_ctor_get(v_a_312_, 0);
lean_inc(v_fvarId_313_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v_a_312_);
v___x_315_ = lean_array_push(v___x_303_, v___x_314_);
v___x_316_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_316_, 0, v_fvarId_313_);
v___x_317_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_296_, v___x_315_, v___x_316_);
lean_dec_ref(v___x_315_);
v_value_247_ = v___x_317_;
v___y_248_ = v_a_234_;
goto v___jp_246_;
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref(v___x_303_);
lean_dec(v_a_245_);
lean_del_object(v___x_240_);
lean_dec_ref(v_type_237_);
lean_dec(v_name_236_);
v_a_318_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_311_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_311_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
else
{
lean_object* v_fvarId_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_del_object(v___x_290_);
v_fvarId_327_ = lean_ctor_get(v_a_301_, 0);
lean_inc(v_fvarId_327_);
lean_dec(v_a_301_);
v___x_328_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_328_, 0, v_fvarId_327_);
v___x_329_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_296_, v___x_303_, v___x_328_);
lean_dec_ref(v___x_303_);
v_value_247_ = v___x_329_;
v___y_248_ = v_a_234_;
goto v___jp_246_;
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_del_object(v___x_290_);
lean_dec(v_fst_288_);
lean_dec(v_a_245_);
lean_del_object(v___x_240_);
lean_dec_ref(v_type_237_);
lean_dec(v_name_236_);
v_a_330_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_300_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_300_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_a_245_);
lean_del_object(v___x_240_);
lean_dec_ref(v_type_237_);
lean_dec(v_name_236_);
v_a_342_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_285_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_285_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
v___jp_246_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_254_; 
v___x_249_ = l_Lean_Compiler_LCNF_mkBoxedName(v_name_236_);
v___x_250_ = lean_box(0);
v___x_251_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_237_);
lean_dec_ref(v_type_237_);
v___x_252_ = 1;
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 3, v_a_245_);
lean_ctor_set(v___x_240_, 2, v___x_251_);
lean_ctor_set(v___x_240_, 1, v___x_250_);
lean_ctor_set(v___x_240_, 0, v___x_249_);
v___x_254_ = v___x_240_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_276_, 3, v_a_245_);
v___x_254_ = v_reuseFailAlloc_276_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
lean_ctor_set_uint8(v___x_254_, sizeof(void*)*4, v___x_252_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v_value_247_);
v___x_256_ = 0;
v___x_257_ = lean_box(0);
v___x_258_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_258_, 0, v___x_254_);
lean_ctor_set(v___x_258_, 1, v___x_255_);
lean_ctor_set(v___x_258_, 2, v___x_257_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*3, v___x_256_);
lean_inc_ref(v___x_258_);
v___x_259_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v___x_258_, v___y_248_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; 
v_unused_267_ = lean_ctor_get(v___x_259_, 0);
lean_dec(v_unused_267_);
v___x_261_ = v___x_259_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_dec(v___x_259_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_258_);
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_258_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_dec_ref_known(v___x_258_, 3);
v_a_268_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_259_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_259_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_del_object(v___x_240_);
lean_dec_ref(v_params_238_);
lean_dec_ref(v_type_237_);
lean_dec(v_name_236_);
v_a_350_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_244_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_244_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___boxed(lean_object* v_sig_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(v_sig_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(lean_object* v_as_367_, size_t v_i_368_, size_t v_stop_369_, lean_object* v_b_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_a_377_; uint8_t v___x_381_; 
v___x_381_ = lean_usize_dec_eq(v_i_368_, v_stop_369_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v_toSignature_383_; lean_object* v___x_384_; 
v___x_382_ = lean_array_uget_borrowed(v_as_367_, v_i_368_);
v_toSignature_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc_ref(v_toSignature_383_);
v___x_384_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_toSignature_383_, v___y_374_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; uint8_t v___x_386_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v___x_386_ = lean_unbox(v_a_385_);
lean_dec(v_a_385_);
if (v___x_386_ == 0)
{
v_a_377_ = v_b_370_;
goto v___jp_376_;
}
else
{
lean_object* v___x_387_; 
lean_inc_ref(v_toSignature_383_);
v___x_387_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(v_toSignature_383_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_389_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_387_, 1);
v___x_389_ = lean_array_push(v_b_370_, v_a_388_);
v_a_377_ = v___x_389_;
goto v___jp_376_;
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec_ref(v_b_370_);
v_a_390_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_387_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_387_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec_ref(v_b_370_);
v_a_398_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_384_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_384_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
else
{
lean_object* v___x_406_; 
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v_b_370_);
return v___x_406_;
}
v___jp_376_:
{
size_t v___x_378_; size_t v___x_379_; 
v___x_378_ = ((size_t)1ULL);
v___x_379_ = lean_usize_add(v_i_368_, v___x_378_);
v_i_368_ = v___x_379_;
v_b_370_ = v_a_377_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0___boxed(lean_object* v_as_407_, lean_object* v_i_408_, lean_object* v_stop_409_, lean_object* v_b_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
size_t v_i_boxed_416_; size_t v_stop_boxed_417_; lean_object* v_res_418_; 
v_i_boxed_416_ = lean_unbox_usize(v_i_408_);
lean_dec(v_i_408_);
v_stop_boxed_417_ = lean_unbox_usize(v_stop_409_);
lean_dec(v_stop_409_);
v_res_418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_407_, v_i_boxed_416_, v_stop_boxed_417_, v_b_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec_ref(v_as_407_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(lean_object* v_as_421_, lean_object* v_start_422_, lean_object* v_stop_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0));
v___x_430_ = lean_nat_dec_lt(v_start_422_, v_stop_423_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_array_get_size(v_as_421_);
v___x_433_ = lean_nat_dec_le(v_stop_423_, v___x_432_);
if (v___x_433_ == 0)
{
uint8_t v___x_434_; 
v___x_434_ = lean_nat_dec_lt(v_start_422_, v___x_432_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_429_);
return v___x_435_;
}
else
{
size_t v___x_436_; size_t v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_usize_of_nat(v_start_422_);
v___x_437_ = lean_usize_of_nat(v___x_432_);
v___x_438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_421_, v___x_436_, v___x_437_, v___x_429_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
return v___x_438_;
}
}
else
{
size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_usize_of_nat(v_start_422_);
v___x_440_ = lean_usize_of_nat(v_stop_423_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_421_, v___x_439_, v___x_440_, v___x_429_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___boxed(lean_object* v_as_442_, lean_object* v_start_443_, lean_object* v_stop_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(v_as_442_, v_start_443_, v_stop_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v_stop_444_);
lean_dec(v_start_443_);
lean_dec_ref(v_as_442_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addBoxedVersions(lean_object* v_decls_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_array_get_size(v_decls_451_);
v___x_459_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(v_decls_451_, v___x_457_, v___x_458_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_468_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_468_ == 0)
{
v___x_462_ = v___x_459_;
v_isShared_463_ = v_isSharedCheck_468_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_468_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = l_Array_append___redArg(v_decls_451_, v_a_460_);
lean_dec(v_a_460_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_464_);
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
else
{
lean_dec_ref(v_decls_451_);
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addBoxedVersions___boxed(lean_object* v_decls_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Compiler_LCNF_addBoxedVersions(v_decls_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(lean_object* v_a_476_){
_start:
{
lean_object* v_currDeclResultType_478_; lean_object* v___x_479_; 
v_currDeclResultType_478_ = lean_ctor_get(v_a_476_, 1);
lean_inc_ref(v_currDeclResultType_478_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v_currDeclResultType_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg___boxed(lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(v_a_480_);
lean_dec_ref(v_a_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_currDeclResultType_490_; lean_object* v___x_491_; 
v_currDeclResultType_490_ = lean_ctor_get(v_a_483_, 1);
lean_inc_ref(v_currDeclResultType_490_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v_currDeclResultType_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___boxed(lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
return v_res_499_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(lean_object* v_t_u2081_500_, lean_object* v_t_u2082_501_){
_start:
{
uint8_t v___y_507_; uint8_t v___x_508_; uint8_t v___x_509_; 
v___x_508_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2081_500_);
v___x_509_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2082_501_);
if (v___x_508_ == 0)
{
if (v___x_509_ == 0)
{
goto v___jp_502_;
}
else
{
v___y_507_ = v___x_508_;
goto v___jp_506_;
}
}
else
{
v___y_507_ = v___x_509_;
goto v___jp_506_;
}
v___jp_502_:
{
uint8_t v___x_503_; uint8_t v___x_504_; 
v___x_503_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2081_500_);
v___x_504_ = lean_bool_not(v___x_503_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; 
v___x_505_ = lean_expr_eqv(v_t_u2081_500_, v_t_u2082_501_);
return v___x_505_;
}
else
{
return v___x_504_;
}
}
v___jp_506_:
{
if (v___y_507_ == 0)
{
return v___y_507_;
}
else
{
goto v___jp_502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing___boxed(lean_object* v_t_u2081_510_, lean_object* v_t_u2082_511_){
_start:
{
uint8_t v_res_512_; lean_object* v_r_513_; 
v_res_512_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_t_u2081_510_, v_t_u2082_511_);
lean_dec_ref(v_t_u2082_511_);
lean_dec_ref(v_t_u2081_510_);
v_r_513_ = lean_box(v_res_512_);
return v_r_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(lean_object* v_x_516_, lean_object* v_xType_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___y_521_; 
if (lean_obj_tag(v_xType_517_) == 4)
{
lean_object* v_declName_560_; 
v_declName_560_ = lean_ctor_get(v_xType_517_, 0);
if (lean_obj_tag(v_declName_560_) == 1)
{
lean_object* v_pre_561_; 
v_pre_561_ = lean_ctor_get(v_declName_560_, 0);
if (lean_obj_tag(v_pre_561_) == 0)
{
lean_object* v_us_562_; lean_object* v_str_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_us_562_ = lean_ctor_get(v_xType_517_, 1);
v_str_563_ = lean_ctor_get(v_declName_560_, 1);
v___x_564_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0));
v___x_565_ = lean_string_dec_eq(v_str_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1));
v___x_567_ = lean_string_dec_eq(v_str_563_, v___x_566_);
if (v___x_567_ == 0)
{
v___y_521_ = v_a_518_;
goto v___jp_520_;
}
else
{
if (lean_obj_tag(v_us_562_) == 0)
{
goto v___jp_557_;
}
else
{
v___y_521_ = v_a_518_;
goto v___jp_520_;
}
}
}
else
{
if (lean_obj_tag(v_us_562_) == 0)
{
goto v___jp_557_;
}
else
{
v___y_521_ = v_a_518_;
goto v___jp_520_;
}
}
}
else
{
v___y_521_ = v_a_518_;
goto v___jp_520_;
}
}
else
{
v___y_521_ = v_a_518_;
goto v___jp_520_;
}
}
else
{
v___y_521_ = v_a_518_;
goto v___jp_520_;
}
v___jp_520_:
{
uint8_t v___x_522_; lean_object* v___x_523_; 
v___x_522_ = 1;
v___x_523_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_522_, v_x_516_, v___y_521_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
if (lean_obj_tag(v_a_524_) == 1)
{
lean_object* v_val_525_; 
v_val_525_ = lean_ctor_get(v_a_524_, 0);
lean_inc(v_val_525_);
lean_dec_ref_known(v_a_524_, 1);
switch(lean_obj_tag(v_val_525_))
{
case 0:
{
lean_dec_ref_known(v_val_525_, 1);
return v___x_523_;
}
case 9:
{
lean_object* v_args_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_args_526_ = lean_ctor_get(v_val_525_, 1);
lean_inc_ref(v_args_526_);
lean_dec_ref_known(v_val_525_, 2);
v___x_527_ = lean_array_get_size(v_args_526_);
lean_dec_ref(v_args_526_);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_nat_dec_eq(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_537_; 
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; 
v_unused_538_ = lean_ctor_get(v___x_523_, 0);
lean_dec(v_unused_538_);
v___x_531_ = v___x_523_;
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
else
{
lean_dec(v___x_523_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = lean_box(0);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
return v___x_523_;
}
}
default: 
{
lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_val_525_);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; 
v_unused_547_ = lean_ctor_get(v___x_523_, 0);
lean_dec(v_unused_547_);
v___x_540_ = v___x_523_;
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
else
{
lean_dec(v___x_523_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_542_ = lean_box(0);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_542_);
v___x_544_ = v___x_540_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
else
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
lean_dec(v_a_524_);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v___x_523_, 0);
lean_dec(v_unused_556_);
v___x_549_ = v___x_523_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_dec(v___x_523_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_box(0);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
return v___x_523_;
}
}
v___jp_557_:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_box(0);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___boxed(lean_object* v_x_568_, lean_object* v_xType_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_x_568_, v_xType_569_, v_a_570_);
lean_dec(v_a_570_);
lean_dec_ref(v_xType_569_);
lean_dec(v_x_568_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(lean_object* v_x_573_, lean_object* v_xType_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_x_573_, v_xType_574_, v_a_578_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___boxed(lean_object* v_x_583_, lean_object* v_xType_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(v_x_583_, v_xType_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec_ref(v_xType_584_);
lean_dec(v_x_583_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(lean_object* v_fvarId_598_, lean_object* v_fvarIdType_599_, lean_object* v_expectedType_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
uint8_t v___x_608_; 
v___x_608_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_expectedType_600_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
v___x_609_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_fvarId_598_, v_fvarIdType_599_, v_a_604_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_734_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_734_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_734_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_734_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
if (lean_obj_tag(v_a_610_) == 0)
{
lean_object* v___x_614_; lean_object* v___x_616_; 
lean_dec_ref(v_expectedType_600_);
v___x_614_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_614_, 0, v_fvarIdType_599_);
lean_ctor_set(v___x_614_, 1, v_fvarId_598_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_614_);
v___x_616_ = v___x_612_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
else
{
lean_object* v_val_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_733_; 
lean_del_object(v___x_612_);
lean_dec(v_fvarId_598_);
v_val_618_ = lean_ctor_get(v_a_610_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v_a_610_);
if (v_isSharedCheck_733_ == 0)
{
v___x_620_ = v_a_610_;
v_isShared_621_ = v_isSharedCheck_733_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_val_618_);
lean_dec(v_a_610_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_733_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = 1;
v___x_623_ = lean_box(0);
lean_inc_ref(v_fvarIdType_599_);
v___x_624_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_622_, v___x_623_, v_fvarIdType_599_, v_val_618_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v_fvarId_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v_fvarId_626_ = lean_ctor_get(v_a_625_, 0);
lean_inc(v_fvarId_626_);
v___x_627_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_627_, 0, v_fvarIdType_599_);
lean_ctor_set(v___x_627_, 1, v_fvarId_626_);
lean_inc_ref(v_expectedType_600_);
v___x_628_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_622_, v___x_623_, v_expectedType_600_, v___x_627_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v_fvarId_630_; lean_object* v___x_631_; lean_object* v_currDecl_632_; lean_object* v_nextAuxIdx_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_715_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
v_fvarId_630_ = lean_ctor_get(v_a_629_, 0);
v___x_631_ = lean_st_ref_get(v_a_602_);
v_currDecl_632_ = lean_ctor_get(v_a_601_, 0);
v_nextAuxIdx_633_ = lean_ctor_get(v___x_631_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v___x_631_, 0);
lean_dec(v_unused_716_);
v___x_635_ = v___x_631_;
v_isShared_636_ = v_isSharedCheck_715_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_nextAuxIdx_633_);
lean_dec(v___x_631_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_715_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
lean_inc(v_fvarId_630_);
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 5);
lean_ctor_set(v___x_620_, 0, v_fvarId_630_);
v___x_638_ = v___x_620_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_fvarId_630_);
v___x_638_ = v_reuseFailAlloc_714_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_640_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v___x_638_);
lean_ctor_set(v___x_635_, 0, v_a_629_);
v___x_640_ = v___x_635_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_629_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_638_);
v___x_640_ = v_reuseFailAlloc_713_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
uint8_t v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_641_ = 1;
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v_a_625_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
v___x_643_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__1));
v___x_644_ = lean_name_append_index_after(v___x_643_, v_nextAuxIdx_633_);
lean_inc(v_currDecl_632_);
v___x_645_ = l_Lean_Name_append(v_currDecl_632_, v___x_644_);
v___x_646_ = lean_box(0);
v___x_647_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__2));
lean_inc(v___x_645_);
v___x_648_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_648_, 0, v___x_645_);
lean_ctor_set(v___x_648_, 1, v___x_646_);
lean_ctor_set(v___x_648_, 2, v_expectedType_600_);
lean_ctor_set(v___x_648_, 3, v___x_647_);
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*4, v___x_641_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_642_);
v___x_650_ = lean_box(0);
v___x_651_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_651_, 0, v___x_648_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
lean_ctor_set(v___x_651_, 2, v___x_650_);
lean_ctor_set_uint8(v___x_651_, sizeof(void*)*3, v___x_608_);
lean_inc_ref(v___x_651_);
v___x_652_ = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(v___x_622_, v___x_651_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
if (lean_obj_tag(v_a_653_) == 0)
{
lean_object* v___x_654_; lean_object* v_auxDecls_655_; lean_object* v_nextAuxIdx_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_685_; 
v___x_654_ = lean_st_ref_take(v_a_602_);
v_auxDecls_655_ = lean_ctor_get(v___x_654_, 0);
v_nextAuxIdx_656_ = lean_ctor_get(v___x_654_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_685_ == 0)
{
v___x_658_ = v___x_654_;
v_isShared_659_ = v_isSharedCheck_685_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_nextAuxIdx_656_);
lean_inc(v_auxDecls_655_);
lean_dec(v___x_654_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_685_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
lean_inc_ref(v___x_651_);
v___x_660_ = lean_array_push(v_auxDecls_655_, v___x_651_);
v___x_661_ = lean_unsigned_to_nat(1u);
v___x_662_ = lean_nat_add(v_nextAuxIdx_656_, v___x_661_);
lean_dec(v_nextAuxIdx_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_662_);
lean_ctor_set(v___x_658_, 0, v___x_660_);
v___x_664_ = v___x_658_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v___x_662_);
v___x_664_ = v_reuseFailAlloc_684_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_st_ref_set(v_a_602_, v___x_664_);
v___x_666_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v___x_651_, v_a_606_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_674_; 
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v___x_666_, 0);
lean_dec(v_unused_675_);
v___x_668_ = v___x_666_;
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
else
{
lean_dec(v___x_666_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_645_);
lean_ctor_set(v___x_670_, 1, v___x_647_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec(v___x_645_);
v_a_676_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_666_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_666_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
else
{
lean_object* v_declName_686_; lean_object* v___x_687_; 
lean_dec(v___x_645_);
v_declName_686_ = lean_ctor_get(v_a_653_, 0);
lean_inc(v_declName_686_);
lean_dec_ref_known(v_a_653_, 1);
v___x_687_ = l_Lean_Compiler_LCNF_eraseDecl(v___x_622_, v___x_651_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_695_; 
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v___x_687_, 0);
lean_dec(v_unused_696_);
v___x_689_ = v___x_687_;
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
else
{
lean_dec(v___x_687_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_691_, 0, v_declName_686_);
lean_ctor_set(v___x_691_, 1, v___x_647_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_691_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec(v_declName_686_);
v_a_697_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_687_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_687_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec_ref_known(v___x_651_, 3);
lean_dec(v___x_645_);
v_a_705_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_652_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_652_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec(v_a_625_);
lean_del_object(v___x_620_);
lean_dec_ref(v_expectedType_600_);
v_a_717_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_628_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_628_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_del_object(v___x_620_);
lean_dec_ref(v_expectedType_600_);
lean_dec_ref(v_fvarIdType_599_);
v_a_725_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_624_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_624_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v_expectedType_600_);
lean_dec_ref(v_fvarIdType_599_);
lean_dec(v_fvarId_598_);
v_a_735_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_609_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_609_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec_ref(v_expectedType_600_);
lean_dec_ref(v_fvarIdType_599_);
v___x_743_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_743_, 0, v_fvarId_598_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___boxed(lean_object* v_fvarId_745_, lean_object* v_fvarIdType_746_, lean_object* v_expectedType_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_745_, v_fvarIdType_746_, v_expectedType_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(lean_object* v_fvarId_756_, lean_object* v_expectedType_757_, lean_object* v_k_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v___x_766_; 
lean_inc(v_fvarId_756_);
v___x_766_ = l_Lean_Compiler_LCNF_getType(v_fvarId_756_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; uint8_t v___x_768_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_767_, v_expectedType_757_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_inc_ref(v_expectedType_757_);
v___x_769_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_756_, v_a_767_, v_expectedType_757_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_769_, 1);
v___x_771_ = 1;
v___x_772_ = lean_box(0);
v___x_773_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_771_, v___x_772_, v_expectedType_757_, v_a_770_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v_fvarId_775_; lean_object* v___x_776_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_773_, 1);
v_fvarId_775_ = lean_ctor_get(v_a_774_, 0);
lean_inc(v_a_764_);
lean_inc_ref(v_a_763_);
lean_inc(v_a_762_);
lean_inc_ref(v_a_761_);
lean_inc(v_a_760_);
lean_inc_ref(v_a_759_);
lean_inc(v_fvarId_775_);
v___x_776_ = lean_apply_8(v_k_758_, v_fvarId_775_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, lean_box(0));
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_785_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_785_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v_a_774_);
lean_ctor_set(v___x_781_, 1, v_a_777_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_781_);
v___x_783_ = v___x_779_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
else
{
lean_dec(v_a_774_);
return v___x_776_;
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_k_758_);
v_a_786_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_773_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_773_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref(v_k_758_);
lean_dec_ref(v_expectedType_757_);
v_a_794_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_769_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_769_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v___x_802_; 
lean_dec(v_a_767_);
lean_dec_ref(v_expectedType_757_);
lean_inc(v_a_764_);
lean_inc_ref(v_a_763_);
lean_inc(v_a_762_);
lean_inc_ref(v_a_761_);
lean_inc(v_a_760_);
lean_inc_ref(v_a_759_);
v___x_802_ = lean_apply_8(v_k_758_, v_fvarId_756_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, lean_box(0));
return v___x_802_;
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec_ref(v_k_758_);
lean_dec_ref(v_expectedType_757_);
lean_dec(v_fvarId_756_);
v_a_803_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_766_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_766_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded___boxed(lean_object* v_fvarId_811_, lean_object* v_expectedType_812_, lean_object* v_k_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(v_fvarId_811_, v_expectedType_812_, v_k_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(lean_object* v_arg_822_, lean_object* v_k_823_, lean_object* v_x_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(v_arg_822_, v_x_824_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
v___x_833_ = lean_apply_8(v_k_823_, v___x_832_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, lean_box(0));
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0___boxed(lean_object* v_arg_834_, lean_object* v_k_835_, lean_object* v_x_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_834_, v_k_835_, v_x_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(lean_object* v_arg_845_, lean_object* v_expectedType_846_, lean_object* v_k_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
if (lean_obj_tag(v_arg_845_) == 0)
{
lean_object* v___x_855_; 
lean_dec_ref(v_expectedType_846_);
lean_inc(v_a_853_);
lean_inc_ref(v_a_852_);
lean_inc(v_a_851_);
lean_inc_ref(v_a_850_);
lean_inc(v_a_849_);
lean_inc_ref(v_a_848_);
v___x_855_ = lean_apply_8(v_k_847_, v_arg_845_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, lean_box(0));
return v___x_855_;
}
else
{
lean_object* v_fvarId_856_; lean_object* v___x_857_; 
v_fvarId_856_ = lean_ctor_get(v_arg_845_, 0);
lean_inc(v_fvarId_856_);
v___x_857_ = l_Lean_Compiler_LCNF_getType(v_fvarId_856_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; uint8_t v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_858_, v_expectedType_846_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
lean_inc_ref(v_expectedType_846_);
lean_inc(v_fvarId_856_);
v___x_860_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_856_, v_a_858_, v_expectedType_846_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v___x_862_ = 1;
v___x_863_ = lean_box(0);
v___x_864_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_862_, v___x_863_, v_expectedType_846_, v_a_861_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v_fvarId_866_; lean_object* v___x_867_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_864_, 1);
v_fvarId_866_ = lean_ctor_get(v_a_865_, 0);
lean_inc(v_fvarId_866_);
v___x_867_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_845_, v_k_847_, v_fvarId_866_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_876_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_876_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_a_865_);
lean_ctor_set(v___x_872_, 1, v_a_868_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_872_);
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
else
{
lean_dec(v_a_865_);
return v___x_867_;
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref_known(v_arg_845_, 1);
lean_dec_ref(v_k_847_);
v_a_877_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_864_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_864_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec_ref_known(v_arg_845_, 1);
lean_dec_ref(v_k_847_);
lean_dec_ref(v_expectedType_846_);
v_a_885_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_860_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_860_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v___x_893_; 
lean_inc(v_fvarId_856_);
lean_dec(v_a_858_);
lean_dec_ref(v_expectedType_846_);
v___x_893_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_845_, v_k_847_, v_fvarId_856_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
return v___x_893_;
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref_known(v_arg_845_, 1);
lean_dec_ref(v_k_847_);
lean_dec_ref(v_expectedType_846_);
v_a_894_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_857_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_857_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___boxed(lean_object* v_arg_902_, lean_object* v_expectedType_903_, lean_object* v_k_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(v_arg_902_, v_expectedType_903_, v_k_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(lean_object* v_upperBound_913_, lean_object* v_args_914_, lean_object* v_typeFromIdx_915_, lean_object* v_a_916_, lean_object* v_b_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_a_926_; uint8_t v___x_930_; 
v___x_930_ = lean_nat_dec_lt(v_a_916_, v_upperBound_913_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
lean_dec(v_a_916_);
lean_dec_ref(v_typeFromIdx_915_);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v_b_917_);
return v___x_931_;
}
else
{
lean_object* v_fst_932_; lean_object* v_snd_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_996_; 
v_fst_932_ = lean_ctor_get(v_b_917_, 0);
v_snd_933_ = lean_ctor_get(v_b_917_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v_b_917_);
if (v_isSharedCheck_996_ == 0)
{
v___x_935_ = v_b_917_;
v_isShared_936_ = v_isSharedCheck_996_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_snd_933_);
lean_inc(v_fst_932_);
lean_dec(v_b_917_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_996_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; 
v___x_937_ = lean_array_fget(v_args_914_, v_a_916_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = lean_array_push(v_fst_932_, v___x_937_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_938_);
v___x_940_ = v___x_935_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_snd_933_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
v_a_926_ = v___x_940_;
goto v___jp_925_;
}
}
else
{
lean_object* v_fvarId_942_; lean_object* v___x_943_; 
v_fvarId_942_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_fvarId_942_);
v___x_943_ = l_Lean_Compiler_LCNF_getType(v_fvarId_942_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v___x_943_, 1);
lean_inc_ref(v_typeFromIdx_915_);
lean_inc(v_a_916_);
v___x_945_ = lean_apply_1(v_typeFromIdx_915_, v_a_916_);
v___x_946_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_944_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_982_; 
lean_inc(v_fvarId_942_);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v___x_937_, 0);
lean_dec(v_unused_983_);
v___x_948_ = v___x_937_;
v_isShared_949_ = v_isSharedCheck_982_;
goto v_resetjp_947_;
}
else
{
lean_dec(v___x_937_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_982_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; 
lean_inc_ref(v___x_945_);
v___x_950_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_942_, v_a_944_, v___x_945_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = 1;
v___x_953_ = lean_box(0);
v___x_954_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_952_, v___x_953_, v___x_945_, v_a_951_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v_fvarId_956_; lean_object* v___x_958_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
v_fvarId_956_ = lean_ctor_get(v_a_955_, 0);
lean_inc(v_fvarId_956_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v_fvarId_956_);
v___x_958_ = v___x_948_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_fvarId_956_);
v___x_958_ = v_reuseFailAlloc_965_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_959_ = lean_array_push(v_fst_932_, v___x_958_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v_a_955_);
v___x_961_ = lean_array_push(v_snd_933_, v___x_960_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 1, v___x_961_);
lean_ctor_set(v___x_935_, 0, v___x_959_);
v___x_963_ = v___x_935_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
v_a_926_ = v___x_963_;
goto v___jp_925_;
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_del_object(v___x_948_);
lean_del_object(v___x_935_);
lean_dec(v_snd_933_);
lean_dec(v_fst_932_);
lean_dec(v_a_916_);
lean_dec_ref(v_typeFromIdx_915_);
v_a_966_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_954_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_954_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_del_object(v___x_948_);
lean_dec_ref(v___x_945_);
lean_del_object(v___x_935_);
lean_dec(v_snd_933_);
lean_dec(v_fst_932_);
lean_dec(v_a_916_);
lean_dec_ref(v_typeFromIdx_915_);
v_a_974_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_950_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_950_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_986_; 
lean_dec_ref(v___x_945_);
lean_dec(v_a_944_);
v___x_984_ = lean_array_push(v_fst_932_, v___x_937_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_984_);
v___x_986_ = v___x_935_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_snd_933_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
v_a_926_ = v___x_986_;
goto v___jp_925_;
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref_known(v___x_937_, 1);
lean_del_object(v___x_935_);
lean_dec(v_snd_933_);
lean_dec(v_fst_932_);
lean_dec(v_a_916_);
lean_dec_ref(v_typeFromIdx_915_);
v_a_988_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_943_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_943_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
}
v___jp_925_:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_add(v_a_916_, v___x_927_);
lean_dec(v_a_916_);
v_a_916_ = v___x_928_;
v_b_917_ = v_a_926_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg___boxed(lean_object* v_upperBound_997_, lean_object* v_args_998_, lean_object* v_typeFromIdx_999_, lean_object* v_a_1000_, lean_object* v_b_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v_upperBound_997_, v_args_998_, v_typeFromIdx_999_, v_a_1000_, v_b_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v_args_998_);
lean_dec(v_upperBound_997_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(lean_object* v_args_1010_, lean_object* v_typeFromIdx_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1019_; lean_object* v_newArgs_1020_; lean_object* v___x_1021_; lean_object* v_casters_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1019_ = lean_array_get_size(v_args_1010_);
v_newArgs_1020_ = lean_mk_empty_array_with_capacity(v___x_1019_);
v___x_1021_ = lean_unsigned_to_nat(0u);
v_casters_1022_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0));
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v_newArgs_1020_);
lean_ctor_set(v___x_1023_, 1, v_casters_1022_);
v___x_1024_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v___x_1019_, v_args_1010_, v_typeFromIdx_1011_, v___x_1021_, v___x_1023_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1041_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1041_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1041_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_fst_1029_; lean_object* v_snd_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1040_; 
v_fst_1029_ = lean_ctor_get(v_a_1025_, 0);
v_snd_1030_ = lean_ctor_get(v_a_1025_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_a_1025_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1032_ = v_a_1025_;
v_isShared_1033_ = v_isSharedCheck_1040_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_snd_1030_);
lean_inc(v_fst_1029_);
lean_dec(v_a_1025_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1040_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_fst_1029_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_snd_1030_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1035_);
v___x_1037_ = v___x_1027_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
else
{
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux___boxed(lean_object* v_args_1042_, lean_object* v_typeFromIdx_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1042_, v_typeFromIdx_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec_ref(v_args_1042_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(lean_object* v_upperBound_1052_, lean_object* v_args_1053_, lean_object* v_typeFromIdx_1054_, lean_object* v_inst_1055_, lean_object* v_R_1056_, lean_object* v_a_1057_, lean_object* v_b_1058_, lean_object* v_c_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v_upperBound_1052_, v_args_1053_, v_typeFromIdx_1054_, v_a_1057_, v_b_1058_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___boxed(lean_object* v_upperBound_1068_, lean_object* v_args_1069_, lean_object* v_typeFromIdx_1070_, lean_object* v_inst_1071_, lean_object* v_R_1072_, lean_object* v_a_1073_, lean_object* v_b_1074_, lean_object* v_c_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(v_upperBound_1068_, v_args_1069_, v_typeFromIdx_1070_, v_inst_1071_, v_R_1072_, v_a_1073_, v_b_1074_, v_c_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec_ref(v_args_1069_);
lean_dec(v_upperBound_1068_);
return v_res_1083_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0(void){
_start:
{
uint8_t v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = 1;
v___x_1085_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(lean_object* v_ps_1086_, lean_object* v_i_1087_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v_type_1090_; 
v___x_1088_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0);
v___x_1089_ = lean_array_get_borrowed(v___x_1088_, v_ps_1086_, v_i_1087_);
v_type_1090_ = lean_ctor_get(v___x_1089_, 2);
lean_inc_ref(v_type_1090_);
return v_type_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed(lean_object* v_ps_1091_, lean_object* v_i_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(v_ps_1091_, v_i_1092_);
lean_dec(v_i_1092_);
lean_dec_ref(v_ps_1091_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(lean_object* v_args_1094_, lean_object* v_ps_1095_, lean_object* v_k_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v___f_1104_; lean_object* v___x_1105_; 
v___f_1104_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1104_, 0, v_ps_1095_);
v___x_1105_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1094_, v___f_1104_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v_fst_1107_; lean_object* v_snd_1108_; lean_object* v___x_1109_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v_fst_1107_ = lean_ctor_get(v_a_1106_, 0);
lean_inc(v_fst_1107_);
v_snd_1108_ = lean_ctor_get(v_a_1106_, 1);
lean_inc(v_snd_1108_);
lean_dec(v_a_1106_);
lean_inc(v_a_1102_);
lean_inc_ref(v_a_1101_);
lean_inc(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc(v_a_1098_);
lean_inc_ref(v_a_1097_);
v___x_1109_ = lean_apply_8(v_k_1096_, v_fst_1107_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, lean_box(0));
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1119_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1119_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1119_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1114_ = 1;
v___x_1115_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1114_, v_snd_1108_, v_a_1110_);
lean_dec(v_snd_1108_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1115_);
v___x_1117_ = v___x_1112_;
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
lean_dec(v_snd_1108_);
return v___x_1109_;
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v_k_1096_);
v_a_1120_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1105_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1105_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___boxed(lean_object* v_args_1128_, lean_object* v_ps_1129_, lean_object* v_k_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(v_args_1128_, v_ps_1129_, v_k_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec_ref(v_args_1128_);
return v_res_1138_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = lean_box(0);
v___x_1143_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1));
v___x_1144_ = l_Lean_Expr_const___override(v___x_1143_, v___x_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(lean_object* v_x_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___boxed(lean_object* v_x_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(v_x_1147_);
lean_dec(v_x_1147_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(lean_object* v_args_1150_, lean_object* v_k_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v___f_1159_; lean_object* v___x_1160_; 
v___f_1159_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0));
v___x_1160_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1150_, v___f_1159_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v_fst_1162_; lean_object* v_snd_1163_; lean_object* v___x_1164_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 1);
v_fst_1162_ = lean_ctor_get(v_a_1161_, 0);
lean_inc(v_fst_1162_);
v_snd_1163_ = lean_ctor_get(v_a_1161_, 1);
lean_inc(v_snd_1163_);
lean_dec(v_a_1161_);
lean_inc(v_a_1157_);
lean_inc_ref(v_a_1156_);
lean_inc(v_a_1155_);
lean_inc_ref(v_a_1154_);
lean_inc(v_a_1153_);
lean_inc_ref(v_a_1152_);
v___x_1164_ = lean_apply_8(v_k_1151_, v_fst_1162_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, lean_box(0));
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1174_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1169_ = 1;
v___x_1170_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1169_, v_snd_1163_, v_a_1165_);
lean_dec(v_snd_1163_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1170_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
else
{
lean_dec(v_snd_1163_);
return v___x_1164_;
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec_ref(v_k_1151_);
v_a_1175_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1160_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1160_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___boxed(lean_object* v_args_1183_, lean_object* v_k_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(v_args_1183_, v_k_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec_ref(v_args_1183_);
return v_res_1192_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0(void){
_start:
{
uint8_t v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = 1;
v___x_1194_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(lean_object* v_msg_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
v___x_1197_ = lean_panic_fn_borrowed(v___x_1196_, v_msg_1195_);
return v___x_1197_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1201_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1202_ = lean_unsigned_to_nat(9u);
v___x_1203_ = lean_unsigned_to_nat(616u);
v___x_1204_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1));
v___x_1205_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0));
v___x_1206_ = l_mkPanicMessageWithDecl(v___x_1205_, v___x_1204_, v___x_1203_, v___x_1202_, v___x_1201_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(lean_object* v_code_1207_, lean_object* v_decl_1208_, lean_object* v_k_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
uint8_t v___y_1216_; lean_object* v_type_1220_; lean_object* v_value_1221_; uint8_t v___x_1222_; 
v_type_1220_ = lean_ctor_get(v_decl_1208_, 2);
v_value_1221_ = lean_ctor_get(v_decl_1208_, 3);
v___x_1222_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_1220_);
if (v___x_1222_ == 0)
{
if (lean_obj_tag(v_code_1207_) == 0)
{
lean_object* v_decl_1223_; lean_object* v_k_1224_; size_t v___x_1225_; size_t v___x_1226_; uint8_t v___x_1227_; 
v_decl_1223_ = lean_ctor_get(v_code_1207_, 0);
v_k_1224_ = lean_ctor_get(v_code_1207_, 1);
v___x_1225_ = lean_ptr_addr(v_k_1224_);
v___x_1226_ = lean_ptr_addr(v_k_1209_);
v___x_1227_ = lean_usize_dec_eq(v___x_1225_, v___x_1226_);
if (v___x_1227_ == 0)
{
v___y_1216_ = v___x_1227_;
goto v___jp_1215_;
}
else
{
size_t v___x_1228_; size_t v___x_1229_; uint8_t v___x_1230_; 
v___x_1228_ = lean_ptr_addr(v_decl_1223_);
v___x_1229_ = lean_ptr_addr(v_decl_1208_);
v___x_1230_ = lean_usize_dec_eq(v___x_1228_, v___x_1229_);
v___y_1216_ = v___x_1230_;
goto v___jp_1215_;
}
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec_ref(v_k_1209_);
lean_dec_ref(v_decl_1208_);
lean_dec_ref(v_code_1207_);
v___x_1231_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_1232_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_1231_);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
}
else
{
uint8_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_dec_ref(v_code_1207_);
v___x_1234_ = 1;
v___x_1235_ = lean_box(0);
v___x_1236_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
lean_inc(v_value_1221_);
v___x_1237_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1234_, v___x_1235_, v___x_1236_, v_value_1221_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v_fvarId_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v_fvarId_1239_ = lean_ctor_get(v_a_1238_, 0);
lean_inc(v_fvarId_1239_);
v___x_1240_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_1240_, 0, v_fvarId_1239_);
v___x_1241_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1234_, v_decl_1208_, v___x_1240_, v_a_1211_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1251_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1251_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1251_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_a_1242_);
lean_ctor_set(v___x_1246_, 1, v_k_1209_);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_a_1238_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1247_);
v___x_1249_ = v___x_1244_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v_a_1238_);
lean_dec_ref(v_k_1209_);
v_a_1252_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1241_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1241_);
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
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v_k_1209_);
lean_dec_ref(v_decl_1208_);
v_a_1260_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1237_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1237_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
v___jp_1215_:
{
if (v___y_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_dec_ref(v_code_1207_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_decl_1208_);
lean_ctor_set(v___x_1217_, 1, v_k_1209_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
else
{
lean_object* v___x_1219_; 
lean_dec_ref(v_k_1209_);
lean_dec_ref(v_decl_1208_);
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v_code_1207_);
return v___x_1219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___boxed(lean_object* v_code_1268_, lean_object* v_decl_1269_, lean_object* v_k_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1268_, v_decl_1269_, v_k_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(lean_object* v_code_1277_, lean_object* v_decl_1278_, lean_object* v_k_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1277_, v_decl_1278_, v_k_1279_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___boxed(lean_object* v_code_1288_, lean_object* v_decl_1289_, lean_object* v_k_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(v_code_1288_, v_decl_1289_, v_k_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(lean_object* v_code_1299_, lean_object* v_decl_1300_, lean_object* v_expType_1301_, lean_object* v_k_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
uint8_t v___y_1311_; lean_object* v_type_1315_; lean_object* v_value_1316_; uint8_t v___x_1317_; 
v_type_1315_ = lean_ctor_get(v_decl_1300_, 2);
v_value_1316_ = lean_ctor_get(v_decl_1300_, 3);
v___x_1317_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_type_1315_, v_expType_1301_);
if (v___x_1317_ == 0)
{
lean_object* v_boxedTy_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec_ref(v_code_1299_);
v_boxedTy_1318_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_1315_);
v___x_1319_ = 1;
v___x_1320_ = lean_box(0);
lean_inc(v_value_1316_);
v___x_1321_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1319_, v___x_1320_, v_boxedTy_1318_, v_value_1316_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v_fvarId_1323_; lean_object* v_type_1324_; lean_object* v___x_1325_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1321_, 1);
v_fvarId_1323_ = lean_ctor_get(v_a_1322_, 0);
v_type_1324_ = lean_ctor_get(v_a_1322_, 2);
lean_inc_ref(v_type_1315_);
lean_inc_ref(v_type_1324_);
lean_inc(v_fvarId_1323_);
v___x_1325_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_1323_, v_type_1324_, v_type_1315_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1319_, v_decl_1300_, v_a_1326_, v_a_1306_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1337_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1337_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1337_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v_a_1328_);
lean_ctor_set(v___x_1332_, 1, v_k_1302_);
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_a_1322_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1333_);
v___x_1335_ = v___x_1330_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec(v_a_1322_);
lean_dec_ref(v_k_1302_);
v_a_1338_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1327_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1327_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_a_1322_);
lean_dec_ref(v_k_1302_);
lean_dec_ref(v_decl_1300_);
v_a_1346_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1325_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1325_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_k_1302_);
lean_dec_ref(v_decl_1300_);
v_a_1354_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1321_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1321_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
if (lean_obj_tag(v_code_1299_) == 0)
{
lean_object* v_decl_1362_; lean_object* v_k_1363_; size_t v___x_1364_; size_t v___x_1365_; uint8_t v___x_1366_; 
v_decl_1362_ = lean_ctor_get(v_code_1299_, 0);
v_k_1363_ = lean_ctor_get(v_code_1299_, 1);
v___x_1364_ = lean_ptr_addr(v_k_1363_);
v___x_1365_ = lean_ptr_addr(v_k_1302_);
v___x_1366_ = lean_usize_dec_eq(v___x_1364_, v___x_1365_);
if (v___x_1366_ == 0)
{
v___y_1311_ = v___x_1366_;
goto v___jp_1310_;
}
else
{
size_t v___x_1367_; size_t v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = lean_ptr_addr(v_decl_1362_);
v___x_1368_ = lean_ptr_addr(v_decl_1300_);
v___x_1369_ = lean_usize_dec_eq(v___x_1367_, v___x_1368_);
v___y_1311_ = v___x_1369_;
goto v___jp_1310_;
}
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec_ref(v_k_1302_);
lean_dec_ref(v_decl_1300_);
lean_dec_ref(v_code_1299_);
v___x_1370_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_1371_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_1370_);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
}
v___jp_1310_:
{
if (v___y_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec_ref(v_code_1299_);
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v_decl_1300_);
lean_ctor_set(v___x_1312_, 1, v_k_1302_);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; 
lean_dec_ref(v_k_1302_);
lean_dec_ref(v_decl_1300_);
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_code_1299_);
return v___x_1314_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded___boxed(lean_object* v_code_1373_, lean_object* v_decl_1374_, lean_object* v_expType_1375_, lean_object* v_k_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(v_code_1373_, v_decl_1374_, v_expType_1375_, v_k_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec_ref(v_expType_1375_);
return v_res_1384_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_instMonadEIO(lean_box(0));
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(lean_object* v_msg_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v_toApplicative_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1463_; 
v___x_1398_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
v___x_1399_ = l_StateRefT_x27_instMonad___redArg(v___x_1398_);
v_toApplicative_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v___x_1399_, 1);
lean_dec(v_unused_1464_);
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1463_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_toApplicative_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1463_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v_toFunctor_1404_; lean_object* v_toSeq_1405_; lean_object* v_toSeqLeft_1406_; lean_object* v_toSeqRight_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1461_; 
v_toFunctor_1404_ = lean_ctor_get(v_toApplicative_1400_, 0);
v_toSeq_1405_ = lean_ctor_get(v_toApplicative_1400_, 2);
v_toSeqLeft_1406_ = lean_ctor_get(v_toApplicative_1400_, 3);
v_toSeqRight_1407_ = lean_ctor_get(v_toApplicative_1400_, 4);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_toApplicative_1400_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_toApplicative_1400_, 1);
lean_dec(v_unused_1462_);
v___x_1409_ = v_toApplicative_1400_;
v_isShared_1410_ = v_isSharedCheck_1461_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_toSeqRight_1407_);
lean_inc(v_toSeqLeft_1406_);
lean_inc(v_toSeq_1405_);
lean_inc(v_toFunctor_1404_);
lean_dec(v_toApplicative_1400_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1461_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___f_1411_; lean_object* v___f_1412_; lean_object* v___f_1413_; lean_object* v___f_1414_; lean_object* v___x_1415_; lean_object* v___f_1416_; lean_object* v___f_1417_; lean_object* v___f_1418_; lean_object* v___x_1420_; 
v___f_1411_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1));
v___f_1412_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1404_);
v___f_1413_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1413_, 0, v_toFunctor_1404_);
v___f_1414_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1414_, 0, v_toFunctor_1404_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___f_1413_);
lean_ctor_set(v___x_1415_, 1, v___f_1414_);
v___f_1416_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1416_, 0, v_toSeqRight_1407_);
v___f_1417_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1417_, 0, v_toSeqLeft_1406_);
v___f_1418_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1418_, 0, v_toSeq_1405_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v___f_1416_);
lean_ctor_set(v___x_1409_, 3, v___f_1417_);
lean_ctor_set(v___x_1409_, 2, v___f_1418_);
lean_ctor_set(v___x_1409_, 1, v___f_1411_);
lean_ctor_set(v___x_1409_, 0, v___x_1415_);
v___x_1420_ = v___x_1409_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___f_1411_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v___f_1418_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v___f_1417_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v___f_1416_);
v___x_1420_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1422_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v___f_1412_);
lean_ctor_set(v___x_1402_, 0, v___x_1420_);
v___x_1422_ = v___x_1402_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___f_1412_);
v___x_1422_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; lean_object* v_toApplicative_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1457_; 
v___x_1423_ = l_StateRefT_x27_instMonad___redArg(v___x_1422_);
v_toApplicative_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v___x_1423_, 1);
lean_dec(v_unused_1458_);
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1457_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_toApplicative_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1457_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v_toFunctor_1428_; lean_object* v_toSeq_1429_; lean_object* v_toSeqLeft_1430_; lean_object* v_toSeqRight_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1455_; 
v_toFunctor_1428_ = lean_ctor_get(v_toApplicative_1424_, 0);
v_toSeq_1429_ = lean_ctor_get(v_toApplicative_1424_, 2);
v_toSeqLeft_1430_ = lean_ctor_get(v_toApplicative_1424_, 3);
v_toSeqRight_1431_ = lean_ctor_get(v_toApplicative_1424_, 4);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_toApplicative_1424_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; 
v_unused_1456_ = lean_ctor_get(v_toApplicative_1424_, 1);
lean_dec(v_unused_1456_);
v___x_1433_ = v_toApplicative_1424_;
v_isShared_1434_ = v_isSharedCheck_1455_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_toSeqRight_1431_);
lean_inc(v_toSeqLeft_1430_);
lean_inc(v_toSeq_1429_);
lean_inc(v_toFunctor_1428_);
lean_dec(v_toApplicative_1424_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1455_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___f_1435_; lean_object* v___f_1436_; lean_object* v___f_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___x_1444_; 
v___f_1435_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3));
v___f_1436_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1428_);
v___f_1437_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1437_, 0, v_toFunctor_1428_);
v___f_1438_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1438_, 0, v_toFunctor_1428_);
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___f_1437_);
lean_ctor_set(v___x_1439_, 1, v___f_1438_);
v___f_1440_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1440_, 0, v_toSeqRight_1431_);
v___f_1441_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1441_, 0, v_toSeqLeft_1430_);
v___f_1442_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1442_, 0, v_toSeq_1429_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 4, v___f_1440_);
lean_ctor_set(v___x_1433_, 3, v___f_1441_);
lean_ctor_set(v___x_1433_, 2, v___f_1442_);
lean_ctor_set(v___x_1433_, 1, v___f_1435_);
lean_ctor_set(v___x_1433_, 0, v___x_1439_);
v___x_1444_ = v___x_1433_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___f_1435_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v___f_1442_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v___f_1441_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v___f_1440_);
v___x_1444_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v___f_1436_);
lean_ctor_set(v___x_1426_, 0, v___x_1444_);
v___x_1446_ = v___x_1426_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___f_1436_);
v___x_1446_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___f_1450_; lean_object* v___x_3271__overap_1451_; lean_object* v___x_1452_; 
v___x_1447_ = l_StateRefT_x27_instMonad___redArg(v___x_1446_);
v___x_1448_ = l_Lean_instInhabitedExpr;
v___x_1449_ = l_instInhabitedOfMonad___redArg(v___x_1447_, v___x_1448_);
v___f_1450_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1450_, 0, v___x_1449_);
v___x_3271__overap_1451_ = lean_panic_fn_borrowed(v___f_1450_, v_msg_1390_);
lean_dec_ref(v___f_1450_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
v___x_1452_ = lean_apply_7(v___x_3271__overap_1451_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, lean_box(0));
return v___x_1452_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___boxed(lean_object* v_msg_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v_msg_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
return v_res_1473_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1476_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1477_ = lean_unsigned_to_nat(44u);
v___x_1478_ = lean_unsigned_to_nat(316u);
v___x_1479_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1));
v___x_1480_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1481_ = l_mkPanicMessageWithDecl(v___x_1480_, v___x_1479_, v___x_1478_, v___x_1477_, v___x_1476_);
return v___x_1481_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = lean_box(0);
v___x_1486_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4));
v___x_1487_ = l_Lean_Expr_const___override(v___x_1486_, v___x_1485_);
return v___x_1487_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = lean_box(0);
v___x_1492_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7));
v___x_1493_ = l_Lean_Expr_const___override(v___x_1492_, v___x_1491_);
return v___x_1493_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = lean_box(0);
v___x_1498_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10));
v___x_1499_ = l_Lean_Expr_const___override(v___x_1498_, v___x_1497_);
return v___x_1499_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1500_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1501_ = lean_unsigned_to_nat(45u);
v___x_1502_ = lean_unsigned_to_nat(301u);
v___x_1503_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1));
v___x_1504_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1505_ = l_mkPanicMessageWithDecl(v___x_1504_, v___x_1503_, v___x_1502_, v___x_1501_, v___x_1500_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(lean_object* v_currentType_1506_, lean_object* v_value_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; 
switch(lean_obj_tag(v_value_1507_))
{
case 0:
{
lean_object* v_value_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1554_; 
v_value_1524_ = lean_ctor_get(v_value_1507_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_value_1507_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1526_ = v_value_1507_;
v_isShared_1527_ = v_isSharedCheck_1554_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_value_1524_);
lean_dec(v_value_1507_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1554_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
switch(lean_obj_tag(v_value_1524_))
{
case 0:
{
lean_object* v_val_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1541_; 
lean_del_object(v___x_1526_);
v_val_1528_ = lean_ctor_get(v_value_1524_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_value_1524_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1530_ = v_value_1524_;
v_isShared_1531_ = v_isSharedCheck_1541_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_val_1528_);
lean_dec(v_value_1524_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1541_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1532_ = l_Lean_maxSmallNat;
v___x_1533_ = lean_nat_dec_le(v_val_1528_, v___x_1532_);
lean_dec(v_val_1528_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1535_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v_currentType_1506_);
v___x_1535_ = v___x_1530_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_currentType_1506_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
lean_dec_ref(v_currentType_1506_);
v___x_1537_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1537_);
v___x_1539_ = v___x_1530_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
case 1:
{
lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1549_; 
lean_del_object(v___x_1526_);
lean_dec_ref(v_currentType_1506_);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_value_1524_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v_value_1524_, 0);
lean_dec(v_unused_1550_);
v___x_1543_ = v_value_1524_;
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
else
{
lean_dec(v_value_1524_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1545_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
if (v_isShared_1544_ == 0)
{
lean_ctor_set_tag(v___x_1543_, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1545_);
v___x_1547_ = v___x_1543_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
default: 
{
lean_object* v___x_1552_; 
lean_dec_ref(v_value_1524_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v_currentType_1506_);
v___x_1552_ = v___x_1526_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_currentType_1506_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec_ref(v_currentType_1506_);
v___x_1555_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
case 5:
{
lean_object* v_i_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_dec_ref(v_currentType_1506_);
v_i_1557_ = lean_ctor_get(v_value_1507_, 0);
lean_inc_ref(v_i_1557_);
lean_dec_ref_known(v_value_1507_, 2);
v___x_1558_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_i_1557_);
lean_dec_ref(v_i_1557_);
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
case 7:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec_ref_known(v_value_1507_, 2);
lean_dec_ref(v_currentType_1506_);
v___x_1560_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11);
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
return v___x_1561_;
}
case 9:
{
lean_object* v_fn_1562_; lean_object* v___x_1563_; 
lean_dec_ref(v_currentType_1506_);
v_fn_1562_ = lean_ctor_get(v_value_1507_, 0);
lean_inc(v_fn_1562_);
lean_dec_ref_known(v_value_1507_, 2);
v___x_1563_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_1562_, v_a_1513_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1575_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1575_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1575_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
if (lean_obj_tag(v_a_1564_) == 1)
{
lean_object* v_val_1568_; lean_object* v_type_1569_; lean_object* v___x_1571_; 
v_val_1568_ = lean_ctor_get(v_a_1564_, 0);
lean_inc(v_val_1568_);
lean_dec_ref_known(v_a_1564_, 1);
v_type_1569_ = lean_ctor_get(v_val_1568_, 2);
lean_inc_ref(v_type_1569_);
lean_dec(v_val_1568_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v_type_1569_);
v___x_1571_ = v___x_1566_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_type_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_del_object(v___x_1566_);
lean_dec(v_a_1564_);
v___x_1573_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12);
v___x_1574_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1573_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1574_;
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
v_a_1576_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1563_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1563_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
case 10:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec_ref_known(v_value_1507_, 2);
lean_dec_ref(v_currentType_1506_);
v___x_1584_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
case 13:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec_ref_known(v_value_1507_, 2);
lean_dec_ref(v_currentType_1506_);
v___x_1586_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
v___x_1587_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1586_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1587_;
}
case 14:
{
lean_dec_ref_known(v_value_1507_, 1);
lean_dec_ref(v_currentType_1506_);
v___y_1516_ = v_a_1508_;
v___y_1517_ = v_a_1509_;
v___y_1518_ = v_a_1510_;
v___y_1519_ = v_a_1511_;
v___y_1520_ = v_a_1512_;
v___y_1521_ = v_a_1513_;
goto v___jp_1515_;
}
case 15:
{
lean_dec_ref_known(v_value_1507_, 1);
lean_dec_ref(v_currentType_1506_);
v___y_1516_ = v_a_1508_;
v___y_1517_ = v_a_1509_;
v___y_1518_ = v_a_1510_;
v___y_1519_ = v_a_1511_;
v___y_1520_ = v_a_1512_;
v___y_1521_ = v_a_1513_;
goto v___jp_1515_;
}
default: 
{
lean_object* v___x_1588_; 
lean_dec(v_value_1507_);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v_currentType_1506_);
return v___x_1588_;
}
}
v___jp_1515_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
v___x_1523_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1522_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___boxed(lean_object* v_currentType_1589_, lean_object* v_value_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(v_currentType_1589_, v_value_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(lean_object* v_msg_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v_toApplicative_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1672_; 
v___x_1607_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
v___x_1608_ = l_StateRefT_x27_instMonad___redArg(v___x_1607_);
v_toApplicative_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1672_ == 0)
{
lean_object* v_unused_1673_; 
v_unused_1673_ = lean_ctor_get(v___x_1608_, 1);
lean_dec(v_unused_1673_);
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1672_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_toApplicative_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1672_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v_toFunctor_1613_; lean_object* v_toSeq_1614_; lean_object* v_toSeqLeft_1615_; lean_object* v_toSeqRight_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1670_; 
v_toFunctor_1613_ = lean_ctor_get(v_toApplicative_1609_, 0);
v_toSeq_1614_ = lean_ctor_get(v_toApplicative_1609_, 2);
v_toSeqLeft_1615_ = lean_ctor_get(v_toApplicative_1609_, 3);
v_toSeqRight_1616_ = lean_ctor_get(v_toApplicative_1609_, 4);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_toApplicative_1609_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; 
v_unused_1671_ = lean_ctor_get(v_toApplicative_1609_, 1);
lean_dec(v_unused_1671_);
v___x_1618_ = v_toApplicative_1609_;
v_isShared_1619_ = v_isSharedCheck_1670_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_toSeqRight_1616_);
lean_inc(v_toSeqLeft_1615_);
lean_inc(v_toSeq_1614_);
lean_inc(v_toFunctor_1613_);
lean_dec(v_toApplicative_1609_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1670_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___f_1620_; lean_object* v___f_1621_; lean_object* v___f_1622_; lean_object* v___f_1623_; lean_object* v___x_1624_; lean_object* v___f_1625_; lean_object* v___f_1626_; lean_object* v___f_1627_; lean_object* v___x_1629_; 
v___f_1620_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1));
v___f_1621_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1613_);
v___f_1622_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1622_, 0, v_toFunctor_1613_);
v___f_1623_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1623_, 0, v_toFunctor_1613_);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___f_1622_);
lean_ctor_set(v___x_1624_, 1, v___f_1623_);
v___f_1625_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1625_, 0, v_toSeqRight_1616_);
v___f_1626_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1626_, 0, v_toSeqLeft_1615_);
v___f_1627_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1627_, 0, v_toSeq_1614_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 4, v___f_1625_);
lean_ctor_set(v___x_1618_, 3, v___f_1626_);
lean_ctor_set(v___x_1618_, 2, v___f_1627_);
lean_ctor_set(v___x_1618_, 1, v___f_1620_);
lean_ctor_set(v___x_1618_, 0, v___x_1624_);
v___x_1629_ = v___x_1618_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v___f_1620_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v___f_1627_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v___f_1626_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v___f_1625_);
v___x_1629_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1631_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 1, v___f_1621_);
lean_ctor_set(v___x_1611_, 0, v___x_1629_);
v___x_1631_ = v___x_1611_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___f_1621_);
v___x_1631_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1632_; lean_object* v_toApplicative_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1666_; 
v___x_1632_ = l_StateRefT_x27_instMonad___redArg(v___x_1631_);
v_toApplicative_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; 
v_unused_1667_ = lean_ctor_get(v___x_1632_, 1);
lean_dec(v_unused_1667_);
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1666_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_toApplicative_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1666_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v_toFunctor_1637_; lean_object* v_toSeq_1638_; lean_object* v_toSeqLeft_1639_; lean_object* v_toSeqRight_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1664_; 
v_toFunctor_1637_ = lean_ctor_get(v_toApplicative_1633_, 0);
v_toSeq_1638_ = lean_ctor_get(v_toApplicative_1633_, 2);
v_toSeqLeft_1639_ = lean_ctor_get(v_toApplicative_1633_, 3);
v_toSeqRight_1640_ = lean_ctor_get(v_toApplicative_1633_, 4);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_toApplicative_1633_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v_toApplicative_1633_, 1);
lean_dec(v_unused_1665_);
v___x_1642_ = v_toApplicative_1633_;
v_isShared_1643_ = v_isSharedCheck_1664_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_toSeqRight_1640_);
lean_inc(v_toSeqLeft_1639_);
lean_inc(v_toSeq_1638_);
lean_inc(v_toFunctor_1637_);
lean_dec(v_toApplicative_1633_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1664_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___f_1644_; lean_object* v___f_1645_; lean_object* v___f_1646_; lean_object* v___f_1647_; lean_object* v___x_1648_; lean_object* v___f_1649_; lean_object* v___f_1650_; lean_object* v___f_1651_; lean_object* v___x_1653_; 
v___f_1644_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3));
v___f_1645_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1637_);
v___f_1646_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1646_, 0, v_toFunctor_1637_);
v___f_1647_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1647_, 0, v_toFunctor_1637_);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___f_1646_);
lean_ctor_set(v___x_1648_, 1, v___f_1647_);
v___f_1649_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1649_, 0, v_toSeqRight_1640_);
v___f_1650_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1650_, 0, v_toSeqLeft_1639_);
v___f_1651_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1651_, 0, v_toSeq_1638_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 4, v___f_1649_);
lean_ctor_set(v___x_1642_, 3, v___f_1650_);
lean_ctor_set(v___x_1642_, 2, v___f_1651_);
lean_ctor_set(v___x_1642_, 1, v___f_1644_);
lean_ctor_set(v___x_1642_, 0, v___x_1648_);
v___x_1653_ = v___x_1642_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___f_1644_);
lean_ctor_set(v_reuseFailAlloc_1663_, 2, v___f_1651_);
lean_ctor_set(v_reuseFailAlloc_1663_, 3, v___f_1650_);
lean_ctor_set(v_reuseFailAlloc_1663_, 4, v___f_1649_);
v___x_1653_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 1, v___f_1645_);
lean_ctor_set(v___x_1635_, 0, v___x_1653_);
v___x_1655_ = v___x_1635_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v___f_1645_);
v___x_1655_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___f_1659_; lean_object* v___x_23546__overap_1660_; lean_object* v___x_1661_; 
v___x_1656_ = l_StateRefT_x27_instMonad___redArg(v___x_1655_);
v___x_1657_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
v___x_1658_ = l_instInhabitedOfMonad___redArg(v___x_1656_, v___x_1657_);
v___f_1659_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1659_, 0, v___x_1658_);
v___x_23546__overap_1660_ = lean_panic_fn_borrowed(v___f_1659_, v_msg_1599_);
lean_dec_ref(v___f_1659_);
lean_inc(v___y_1605_);
lean_inc_ref(v___y_1604_);
lean_inc(v___y_1603_);
lean_inc_ref(v___y_1602_);
lean_inc(v___y_1601_);
lean_inc_ref(v___y_1600_);
v___x_1661_ = lean_apply_7(v___x_23546__overap_1660_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, lean_box(0));
return v___x_1661_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0___boxed(lean_object* v_msg_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v_msg_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(lean_object* v_x_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0___boxed(lean_object* v_x_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(v_x_1685_);
lean_dec(v_x_1685_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2(uint8_t v___x_1687_, lean_object* v_params_1688_, lean_object* v_i_1689_){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v_type_1692_; 
v___x_1690_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_1687_);
v___x_1691_ = lean_array_get(v___x_1690_, v_params_1688_, v_i_1689_);
lean_dec_ref(v___x_1690_);
v_type_1692_ = lean_ctor_get(v___x_1691_, 2);
lean_inc_ref(v_type_1692_);
lean_dec(v___x_1691_);
return v_type_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2___boxed(lean_object* v___x_1693_, lean_object* v_params_1694_, lean_object* v_i_1695_){
_start:
{
uint8_t v___x_24686__boxed_1696_; lean_object* v_res_1697_; 
v___x_24686__boxed_1696_ = lean_unbox(v___x_1693_);
v_res_1697_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2(v___x_24686__boxed_1696_, v_params_1694_, v_i_1695_);
lean_dec(v_i_1695_);
lean_dec_ref(v_params_1694_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(lean_object* v_fvarId_1698_, lean_object* v_code_1699_, lean_object* v_fvarId_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = l_Lean_instBEqFVarId_beq(v_fvarId_1698_, v_fvarId_1700_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec_ref(v_code_1699_);
v___x_1709_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_fvarId_1700_);
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
return v___x_1710_;
}
else
{
lean_object* v___x_1711_; 
lean_dec(v_fvarId_1700_);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_code_1699_);
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2___boxed(lean_object* v_fvarId_1712_, lean_object* v_code_1713_, lean_object* v_fvarId_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_1712_, v_code_1713_, v_fvarId_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v_fvarId_1712_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(lean_object* v_typeName_1723_, lean_object* v_a_1724_, lean_object* v_discr_1725_, lean_object* v_code_1726_, lean_object* v_alts_1727_, lean_object* v_resultType_1728_, lean_object* v_discr_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_currDeclResultType_1737_; uint8_t v___y_1743_; size_t v___x_1746_; size_t v___x_1747_; uint8_t v___x_1748_; 
v_currDeclResultType_1737_ = lean_ctor_get(v___y_1730_, 1);
v___x_1746_ = lean_ptr_addr(v_alts_1727_);
v___x_1747_ = lean_ptr_addr(v_a_1724_);
v___x_1748_ = lean_usize_dec_eq(v___x_1746_, v___x_1747_);
if (v___x_1748_ == 0)
{
v___y_1743_ = v___x_1748_;
goto v___jp_1742_;
}
else
{
size_t v___x_1749_; size_t v___x_1750_; uint8_t v___x_1751_; 
v___x_1749_ = lean_ptr_addr(v_resultType_1728_);
v___x_1750_ = lean_ptr_addr(v_currDeclResultType_1737_);
v___x_1751_ = lean_usize_dec_eq(v___x_1749_, v___x_1750_);
v___y_1743_ = v___x_1751_;
goto v___jp_1742_;
}
v___jp_1738_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_inc_ref(v_currDeclResultType_1737_);
v___x_1739_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1739_, 0, v_typeName_1723_);
lean_ctor_set(v___x_1739_, 1, v_currDeclResultType_1737_);
lean_ctor_set(v___x_1739_, 2, v_discr_1729_);
lean_ctor_set(v___x_1739_, 3, v_a_1724_);
v___x_1740_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
v___jp_1742_:
{
if (v___y_1743_ == 0)
{
lean_dec_ref(v_code_1726_);
goto v___jp_1738_;
}
else
{
uint8_t v___x_1744_; 
v___x_1744_ = l_Lean_instBEqFVarId_beq(v_discr_1725_, v_discr_1729_);
if (v___x_1744_ == 0)
{
lean_dec_ref(v_code_1726_);
goto v___jp_1738_;
}
else
{
lean_object* v___x_1745_; 
lean_dec(v_discr_1729_);
lean_dec_ref(v_a_1724_);
lean_dec(v_typeName_1723_);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_code_1726_);
return v___x_1745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1___boxed(lean_object* v_typeName_1752_, lean_object* v_a_1753_, lean_object* v_discr_1754_, lean_object* v_code_1755_, lean_object* v_alts_1756_, lean_object* v_resultType_1757_, lean_object* v_discr_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_1752_, v_a_1753_, v_discr_1754_, v_code_1755_, v_alts_1756_, v_resultType_1757_, v_discr_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec_ref(v_resultType_1757_);
lean_dec_ref(v_alts_1756_);
lean_dec(v_discr_1754_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(lean_object* v_alt_1767_, lean_object* v_f_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v___y_1777_; 
switch(lean_obj_tag(v_alt_1767_))
{
case 0:
{
lean_object* v_code_1796_; 
v_code_1796_ = lean_ctor_get(v_alt_1767_, 2);
lean_inc_ref(v_code_1796_);
v___y_1777_ = v_code_1796_;
goto v___jp_1776_;
}
case 1:
{
lean_object* v_code_1797_; 
v_code_1797_ = lean_ctor_get(v_alt_1767_, 1);
lean_inc_ref(v_code_1797_);
v___y_1777_ = v_code_1797_;
goto v___jp_1776_;
}
default: 
{
lean_object* v_code_1798_; 
v_code_1798_ = lean_ctor_get(v_alt_1767_, 0);
lean_inc_ref(v_code_1798_);
v___y_1777_ = v_code_1798_;
goto v___jp_1776_;
}
}
v___jp_1776_:
{
lean_object* v___x_1778_; 
lean_inc(v___y_1774_);
lean_inc_ref(v___y_1773_);
lean_inc(v___y_1772_);
lean_inc_ref(v___y_1771_);
lean_inc(v___y_1770_);
lean_inc_ref(v___y_1769_);
v___x_1778_ = lean_apply_8(v_f_1768_, v___y_1777_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, lean_box(0));
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1787_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1787_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1787_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1783_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1767_, v_a_1779_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1783_);
v___x_1785_ = v___x_1781_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v_alt_1767_);
v_a_1788_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1778_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1778_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg___boxed(lean_object* v_alt_1799_, lean_object* v_f_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_alt_1799_, v_f_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(lean_object* v_fvarId_1809_, lean_object* v_i_1810_, lean_object* v_offset_1811_, lean_object* v_ty_1812_, lean_object* v_a_1813_, lean_object* v_y_1814_, lean_object* v_k_1815_, lean_object* v_code_1816_, lean_object* v_y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
uint8_t v___y_1826_; size_t v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = lean_ptr_addr(v_fvarId_1809_);
v___x_1848_ = lean_usize_dec_eq(v___x_1847_, v___x_1847_);
if (v___x_1848_ == 0)
{
v___y_1826_ = v___x_1848_;
goto v___jp_1825_;
}
else
{
uint8_t v___x_1849_; 
v___x_1849_ = lean_nat_dec_eq(v_i_1810_, v_i_1810_);
v___y_1826_ = v___x_1849_;
goto v___jp_1825_;
}
v___jp_1825_:
{
if (v___y_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec_ref(v_code_1816_);
v___x_1827_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1827_, 0, v_fvarId_1809_);
lean_ctor_set(v___x_1827_, 1, v_i_1810_);
lean_ctor_set(v___x_1827_, 2, v_offset_1811_);
lean_ctor_set(v___x_1827_, 3, v_y_1817_);
lean_ctor_set(v___x_1827_, 4, v_ty_1812_);
lean_ctor_set(v___x_1827_, 5, v_a_1813_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
else
{
uint8_t v___x_1829_; 
v___x_1829_ = lean_nat_dec_eq(v_offset_1811_, v_offset_1811_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref(v_code_1816_);
v___x_1830_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1830_, 0, v_fvarId_1809_);
lean_ctor_set(v___x_1830_, 1, v_i_1810_);
lean_ctor_set(v___x_1830_, 2, v_offset_1811_);
lean_ctor_set(v___x_1830_, 3, v_y_1817_);
lean_ctor_set(v___x_1830_, 4, v_ty_1812_);
lean_ctor_set(v___x_1830_, 5, v_a_1813_);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
else
{
size_t v___x_1832_; size_t v___x_1833_; uint8_t v___x_1834_; 
v___x_1832_ = lean_ptr_addr(v_y_1814_);
v___x_1833_ = lean_ptr_addr(v_y_1817_);
v___x_1834_ = lean_usize_dec_eq(v___x_1832_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec_ref(v_code_1816_);
v___x_1835_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1835_, 0, v_fvarId_1809_);
lean_ctor_set(v___x_1835_, 1, v_i_1810_);
lean_ctor_set(v___x_1835_, 2, v_offset_1811_);
lean_ctor_set(v___x_1835_, 3, v_y_1817_);
lean_ctor_set(v___x_1835_, 4, v_ty_1812_);
lean_ctor_set(v___x_1835_, 5, v_a_1813_);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
else
{
size_t v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = lean_ptr_addr(v_ty_1812_);
v___x_1838_ = lean_usize_dec_eq(v___x_1837_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_dec_ref(v_code_1816_);
v___x_1839_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1839_, 0, v_fvarId_1809_);
lean_ctor_set(v___x_1839_, 1, v_i_1810_);
lean_ctor_set(v___x_1839_, 2, v_offset_1811_);
lean_ctor_set(v___x_1839_, 3, v_y_1817_);
lean_ctor_set(v___x_1839_, 4, v_ty_1812_);
lean_ctor_set(v___x_1839_, 5, v_a_1813_);
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
return v___x_1840_;
}
else
{
size_t v___x_1841_; size_t v___x_1842_; uint8_t v___x_1843_; 
v___x_1841_ = lean_ptr_addr(v_k_1815_);
v___x_1842_ = lean_ptr_addr(v_a_1813_);
v___x_1843_ = lean_usize_dec_eq(v___x_1841_, v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec_ref(v_code_1816_);
v___x_1844_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1844_, 0, v_fvarId_1809_);
lean_ctor_set(v___x_1844_, 1, v_i_1810_);
lean_ctor_set(v___x_1844_, 2, v_offset_1811_);
lean_ctor_set(v___x_1844_, 3, v_y_1817_);
lean_ctor_set(v___x_1844_, 4, v_ty_1812_);
lean_ctor_set(v___x_1844_, 5, v_a_1813_);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; 
lean_dec(v_y_1817_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_ty_1812_);
lean_dec(v_offset_1811_);
lean_dec(v_i_1810_);
lean_dec(v_fvarId_1809_);
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v_code_1816_);
return v___x_1846_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4___boxed(lean_object* v_fvarId_1850_, lean_object* v_i_1851_, lean_object* v_offset_1852_, lean_object* v_ty_1853_, lean_object* v_a_1854_, lean_object* v_y_1855_, lean_object* v_k_1856_, lean_object* v_code_1857_, lean_object* v_y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_1850_, v_i_1851_, v_offset_1852_, v_ty_1853_, v_a_1854_, v_y_1855_, v_k_1856_, v_code_1857_, v_y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec_ref(v_k_1856_);
lean_dec(v_y_1855_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(lean_object* v_fvarId_1867_, lean_object* v_i_1868_, lean_object* v_a_1869_, lean_object* v_y_1870_, lean_object* v_k_1871_, lean_object* v_code_1872_, lean_object* v_y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
uint8_t v___y_1882_; size_t v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = lean_ptr_addr(v_fvarId_1867_);
v___x_1897_ = lean_usize_dec_eq(v___x_1896_, v___x_1896_);
if (v___x_1897_ == 0)
{
v___y_1882_ = v___x_1897_;
goto v___jp_1881_;
}
else
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_nat_dec_eq(v_i_1868_, v_i_1868_);
v___y_1882_ = v___x_1898_;
goto v___jp_1881_;
}
v___jp_1881_:
{
if (v___y_1882_ == 0)
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_dec_ref(v_code_1872_);
v___x_1883_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1883_, 0, v_fvarId_1867_);
lean_ctor_set(v___x_1883_, 1, v_i_1868_);
lean_ctor_set(v___x_1883_, 2, v_y_1873_);
lean_ctor_set(v___x_1883_, 3, v_a_1869_);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
else
{
size_t v___x_1885_; size_t v___x_1886_; uint8_t v___x_1887_; 
v___x_1885_ = lean_ptr_addr(v_y_1870_);
v___x_1886_ = lean_ptr_addr(v_y_1873_);
v___x_1887_ = lean_usize_dec_eq(v___x_1885_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec_ref(v_code_1872_);
v___x_1888_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1888_, 0, v_fvarId_1867_);
lean_ctor_set(v___x_1888_, 1, v_i_1868_);
lean_ctor_set(v___x_1888_, 2, v_y_1873_);
lean_ctor_set(v___x_1888_, 3, v_a_1869_);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
else
{
size_t v___x_1890_; size_t v___x_1891_; uint8_t v___x_1892_; 
v___x_1890_ = lean_ptr_addr(v_k_1871_);
v___x_1891_ = lean_ptr_addr(v_a_1869_);
v___x_1892_ = lean_usize_dec_eq(v___x_1890_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_dec_ref(v_code_1872_);
v___x_1893_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1893_, 0, v_fvarId_1867_);
lean_ctor_set(v___x_1893_, 1, v_i_1868_);
lean_ctor_set(v___x_1893_, 2, v_y_1873_);
lean_ctor_set(v___x_1893_, 3, v_a_1869_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
else
{
lean_object* v___x_1895_; 
lean_dec(v_y_1873_);
lean_dec_ref(v_a_1869_);
lean_dec(v_i_1868_);
lean_dec(v_fvarId_1867_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v_code_1872_);
return v___x_1895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3___boxed(lean_object* v_fvarId_1899_, lean_object* v_i_1900_, lean_object* v_a_1901_, lean_object* v_y_1902_, lean_object* v_k_1903_, lean_object* v_code_1904_, lean_object* v_y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_1899_, v_i_1900_, v_a_1901_, v_y_1902_, v_k_1903_, v_code_1904_, v_y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec_ref(v_k_1903_);
lean_dec(v_y_1902_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(uint8_t v___x_1914_, lean_object* v_params_1915_, lean_object* v_i_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v_type_1919_; 
v___x_1917_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_1914_);
v___x_1918_ = lean_array_get(v___x_1917_, v_params_1915_, v_i_1916_);
lean_dec_ref(v___x_1917_);
v_type_1919_ = lean_ctor_get(v___x_1918_, 2);
lean_inc_ref(v_type_1919_);
lean_dec(v___x_1918_);
return v_type_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed(lean_object* v___x_1920_, lean_object* v_params_1921_, lean_object* v_i_1922_){
_start:
{
uint8_t v___x_25023__boxed_1923_; lean_object* v_res_1924_; 
v___x_25023__boxed_1923_ = lean_unbox(v___x_1920_);
v_res_1924_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(v___x_25023__boxed_1923_, v_params_1921_, v_i_1922_);
lean_dec(v_i_1922_);
lean_dec_ref(v_params_1921_);
return v_res_1924_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1926_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1927_ = lean_unsigned_to_nat(44u);
v___x_1928_ = lean_unsigned_to_nat(353u);
v___x_1929_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_1930_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1931_ = l_mkPanicMessageWithDecl(v___x_1930_, v___x_1929_, v___x_1928_, v___x_1927_, v___x_1926_);
return v___x_1931_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1933_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1934_ = lean_unsigned_to_nat(45u);
v___x_1935_ = lean_unsigned_to_nat(336u);
v___x_1936_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_1937_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1938_ = l_mkPanicMessageWithDecl(v___x_1937_, v___x_1936_, v___x_1935_, v___x_1934_, v___x_1933_);
return v___x_1938_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1939_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1940_ = lean_unsigned_to_nat(45u);
v___x_1941_ = lean_unsigned_to_nat(341u);
v___x_1942_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_1943_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1944_ = l_mkPanicMessageWithDecl(v___x_1943_, v___x_1942_, v___x_1941_, v___x_1940_, v___x_1939_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(lean_object* v_code_1945_, lean_object* v_decl_1946_, lean_object* v_k_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v_type_1964_; lean_object* v_value_1965_; lean_object* v___x_1966_; 
v_type_1964_ = lean_ctor_get(v_decl_1946_, 2);
v_value_1965_ = lean_ctor_get(v_decl_1946_, 3);
lean_inc_n(v_value_1965_, 2);
lean_inc_ref(v_type_1964_);
v___x_1966_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(v_type_1964_, v_value_1965_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2376_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_2376_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2376_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
uint8_t v___x_1971_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___x_1984_; 
v___x_1971_ = 1;
lean_inc(v_a_1967_);
v___x_1984_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_1971_, v_decl_1946_, v_a_1967_, v_value_1965_, v_a_1951_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2367_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_1987_ = v___x_1984_;
v_isShared_1988_ = v_isSharedCheck_2367_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1984_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2367_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; 
v___x_1989_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2366_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2366_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2366_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___y_1995_; lean_object* v___y_1996_; uint8_t v___y_1997_; lean_object* v___y_2000_; lean_object* v___y_2001_; uint8_t v___y_2002_; lean_object* v___y_2005_; uint8_t v___y_2006_; lean_object* v___y_2015_; uint8_t v___y_2016_; lean_object* v_value_2024_; lean_object* v___y_2026_; 
v_value_2024_ = lean_ctor_get(v_a_1985_, 3);
switch(lean_obj_tag(v_value_2024_))
{
case 4:
{
lean_object* v_args_2055_; lean_object* v___f_2056_; lean_object* v___x_2057_; 
lean_del_object(v___x_1992_);
lean_del_object(v___x_1987_);
lean_del_object(v___x_1969_);
lean_dec(v_a_1967_);
v_args_2055_ = lean_ctor_get(v_value_2024_, 1);
v___f_2056_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2));
v___x_2057_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2055_, v___f_2056_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v_fst_2059_; lean_object* v_snd_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___x_2057_, 1);
v_fst_2059_ = lean_ctor_get(v_a_2058_, 0);
lean_inc(v_fst_2059_);
v_snd_2060_ = lean_ctor_get(v_a_2058_, 1);
lean_inc(v_snd_2060_);
lean_dec(v_a_2058_);
lean_inc_ref(v_value_2024_);
v___x_2061_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_1971_, v_value_2024_, v_fst_2059_);
v___x_2062_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1971_, v_a_1985_, v___x_2061_, v_a_1951_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2064_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1945_, v_a_2063_, v_a_1990_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2073_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2069_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1971_, v_snd_2060_, v_a_2065_);
lean_dec(v_snd_2060_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2069_);
v___x_2071_ = v___x_2067_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
else
{
lean_dec(v_snd_2060_);
return v___x_2064_;
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_snd_2060_);
lean_dec(v_a_1990_);
lean_dec_ref(v_code_1945_);
v_a_2074_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2062_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2062_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_a_1990_);
lean_dec(v_a_1985_);
lean_dec_ref(v_code_1945_);
v_a_2082_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2057_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2057_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
case 5:
{
lean_object* v_i_2090_; lean_object* v_args_2091_; lean_object* v___f_2092_; uint8_t v___y_2094_; uint8_t v___x_2159_; 
lean_del_object(v___x_1987_);
v_i_2090_ = lean_ctor_get(v_value_2024_, 0);
v_args_2091_ = lean_ctor_get(v_value_2024_, 1);
v___f_2092_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2));
v___x_2159_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_i_2090_);
if (v___x_2159_ == 0)
{
v___y_2094_ = v___x_2159_;
goto v___jp_2093_;
}
else
{
uint8_t v___x_2160_; 
v___x_2160_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_1967_);
v___y_2094_ = v___x_2160_;
goto v___jp_2093_;
}
v___jp_2093_:
{
if (v___y_2094_ == 0)
{
lean_object* v___x_2095_; 
lean_del_object(v___x_1992_);
lean_dec(v_a_1967_);
v___x_2095_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2091_, v___f_2092_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v_fst_2097_; lean_object* v_snd_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v_fst_2097_ = lean_ctor_get(v_a_2096_, 0);
lean_inc(v_fst_2097_);
v_snd_2098_ = lean_ctor_get(v_a_2096_, 1);
lean_inc(v_snd_2098_);
lean_dec(v_a_2096_);
lean_inc_ref(v_value_2024_);
v___x_2099_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_1971_, v_value_2024_, v_fst_2097_);
v___x_2100_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1971_, v_a_1985_, v___x_2099_, v_a_1951_);
if (lean_obj_tag(v___x_2100_) == 0)
{
if (lean_obj_tag(v_code_1945_) == 0)
{
lean_object* v_a_2101_; lean_object* v_decl_2102_; lean_object* v_k_2103_; size_t v___x_2104_; size_t v___x_2105_; uint8_t v___x_2106_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v_decl_2102_ = lean_ctor_get(v_code_1945_, 0);
v_k_2103_ = lean_ctor_get(v_code_1945_, 1);
v___x_2104_ = lean_ptr_addr(v_k_2103_);
v___x_2105_ = lean_ptr_addr(v_a_1990_);
v___x_2106_ = lean_usize_dec_eq(v___x_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
v___y_2000_ = v_snd_2098_;
v___y_2001_ = v_a_2101_;
v___y_2002_ = v___x_2106_;
goto v___jp_1999_;
}
else
{
size_t v___x_2107_; size_t v___x_2108_; uint8_t v___x_2109_; 
v___x_2107_ = lean_ptr_addr(v_decl_2102_);
v___x_2108_ = lean_ptr_addr(v_a_2101_);
v___x_2109_ = lean_usize_dec_eq(v___x_2107_, v___x_2108_);
v___y_2000_ = v_snd_2098_;
v___y_2001_ = v_a_2101_;
v___y_2002_ = v___x_2109_;
goto v___jp_1999_;
}
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
lean_dec_ref_known(v___x_2100_, 1);
lean_dec(v_a_1990_);
lean_dec_ref(v_code_1945_);
v___x_2110_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2111_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2110_);
v___y_1973_ = v_snd_2098_;
v___y_1974_ = v___x_2111_;
goto v___jp_1972_;
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_snd_2098_);
lean_dec(v_a_1990_);
lean_del_object(v___x_1969_);
lean_dec_ref(v_code_1945_);
v_a_2112_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2100_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2100_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_a_1990_);
lean_dec(v_a_1985_);
lean_del_object(v___x_1969_);
lean_dec_ref(v_code_1945_);
v_a_2120_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2095_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2095_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v_cidx_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_del_object(v___x_1969_);
v_cidx_2128_ = lean_ctor_get(v_i_2090_, 1);
v___x_2129_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_1967_, v_cidx_2128_);
lean_dec(v_a_1967_);
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
v___x_2131_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1971_, v_a_1985_, v___x_2130_, v_a_1951_);
if (lean_obj_tag(v___x_2131_) == 0)
{
if (lean_obj_tag(v_code_1945_) == 0)
{
lean_object* v_a_2132_; lean_object* v_decl_2133_; lean_object* v_k_2134_; size_t v___x_2135_; size_t v___x_2136_; uint8_t v___x_2137_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v_decl_2133_ = lean_ctor_get(v_code_1945_, 0);
v_k_2134_ = lean_ctor_get(v_code_1945_, 1);
v___x_2135_ = lean_ptr_addr(v_k_2134_);
v___x_2136_ = lean_ptr_addr(v_a_1990_);
v___x_2137_ = lean_usize_dec_eq(v___x_2135_, v___x_2136_);
if (v___x_2137_ == 0)
{
v___y_2005_ = v_a_2132_;
v___y_2006_ = v___x_2137_;
goto v___jp_2004_;
}
else
{
size_t v___x_2138_; size_t v___x_2139_; uint8_t v___x_2140_; 
v___x_2138_ = lean_ptr_addr(v_decl_2133_);
v___x_2139_ = lean_ptr_addr(v_a_2132_);
v___x_2140_ = lean_usize_dec_eq(v___x_2138_, v___x_2139_);
v___y_2005_ = v_a_2132_;
v___y_2006_ = v___x_2140_;
goto v___jp_2004_;
}
}
else
{
lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2149_; 
lean_del_object(v___x_1992_);
lean_dec(v_a_1990_);
lean_dec_ref(v_code_1945_);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2149_ == 0)
{
lean_object* v_unused_2150_; 
v_unused_2150_ = lean_ctor_get(v___x_2131_, 0);
lean_dec(v_unused_2150_);
v___x_2142_ = v___x_2131_;
v_isShared_2143_ = v_isSharedCheck_2149_;
goto v_resetjp_2141_;
}
else
{
lean_dec(v___x_2131_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2149_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2144_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2145_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2144_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2145_);
v___x_2147_ = v___x_2142_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_del_object(v___x_1992_);
lean_dec(v_a_1990_);
lean_dec_ref(v_code_1945_);
v_a_2151_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2131_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2131_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
}
case 6:
{
lean_inc_ref(v_value_2024_);
lean_del_object(v___x_1992_);
lean_del_object(v___x_1969_);
v___y_2026_ = v_a_1951_;
goto v___jp_2025_;
}
case 7:
{
lean_inc_ref(v_value_2024_);
lean_del_object(v___x_1992_);
lean_del_object(v___x_1969_);
v___y_2026_ = v_a_1951_;
goto v___jp_2025_;
}
case 9:
{
lean_object* v_fn_2161_; lean_object* v_args_2162_; lean_object* v___x_2163_; 
lean_del_object(v___x_1992_);
lean_del_object(v___x_1987_);
lean_del_object(v___x_1969_);
lean_dec(v_a_1967_);
v_fn_2161_ = lean_ctor_get(v_value_2024_, 0);
v_args_2162_ = lean_ctor_get(v_value_2024_, 1);
lean_inc(v_fn_2161_);
v___x_2163_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_2161_, v_a_1953_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
if (lean_obj_tag(v_a_2164_) == 1)
{
lean_object* v_val_2165_; lean_object* v_type_2166_; lean_object* v_params_2167_; lean_object* v___x_2168_; lean_object* v___f_2169_; lean_object* v___x_2170_; 
v_val_2165_ = lean_ctor_get(v_a_2164_, 0);
lean_inc(v_val_2165_);
lean_dec_ref_known(v_a_2164_, 1);
v_type_2166_ = lean_ctor_get(v_val_2165_, 2);
lean_inc_ref(v_type_2166_);
v_params_2167_ = lean_ctor_get(v_val_2165_, 3);
lean_inc_ref(v_params_2167_);
lean_dec(v_val_2165_);
v___x_2168_ = lean_box(v___x_1971_);
v___f_2169_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2___boxed), 3, 2);
lean_closure_set(v___f_2169_, 0, v___x_2168_);
lean_closure_set(v___f_2169_, 1, v_params_2167_);
v___x_2170_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2162_, v___f_2169_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v_fst_2172_; lean_object* v_snd_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v_fst_2172_ = lean_ctor_get(v_a_2171_, 0);
lean_inc(v_fst_2172_);
v_snd_2173_ = lean_ctor_get(v_a_2171_, 1);
lean_inc(v_snd_2173_);
lean_dec(v_a_2171_);
lean_inc_ref(v_value_2024_);
v___x_2174_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_1971_, v_value_2024_, v_fst_2172_);
v___x_2175_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1971_, v_a_1985_, v___x_2174_, v_a_1951_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2177_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(v_code_1945_, v_a_2176_, v_type_2166_, v_a_1990_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
lean_dec_ref(v_type_2166_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2186_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2186_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2186_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2182_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1971_, v_snd_2173_, v_a_2178_);
lean_dec(v_snd_2173_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2182_);
v___x_2184_ = v___x_2180_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
else
{
lean_dec(v_snd_2173_);
return v___x_2177_;
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_snd_2173_);
lean_dec_ref(v_type_2166_);
lean_dec(v_a_1990_);
lean_dec_ref(v_code_1945_);
v_a_2187_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2175_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2175_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec_ref(v_type_2166_);
lean_dec(v_a_1990_);
lean_dec(v_a_1985_);
lean_dec_ref(v_code_1945_);
v_a_2195_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2170_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2170_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec(v_a_2164_);
lean_dec(v_a_1990_);
lean_dec(v_a_1985_);
lean_dec_ref(v_code_1945_);
v___x_2203_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3);
v___x_2204_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2203_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
return v___x_2204_;
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_a_1990_);
lean_dec(v_a_1985_);
lean_dec_ref(v_code_1945_);
v_a_2205_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2163_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2163_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
case 10:
{
lean_object* v_fn_2213_; lean_object* v_args_2214_; lean_object* v___x_2215_; 
lean_del_object(v___x_1992_);
lean_del_object(v___x_1987_);
lean_del_object(v___x_1969_);
lean_dec(v_a_1967_);
v_fn_2213_ = lean_ctor_get(v_value_2024_, 0);
v_args_2214_ = lean_ctor_get(v_value_2024_, 1);
lean_inc(v_fn_2213_);
v___x_2215_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_2213_, v_a_1953_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
if (lean_obj_tag(v_a_2216_) == 1)
{
lean_object* v_val_2217_; lean_object* v___x_2218_; 
v_val_2217_ = lean_ctor_get(v_a_2216_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v_a_2216_, 1);
v___x_2218_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_val_2217_, v_a_1953_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v___f_2220_; lean_object* v___y_2222_; uint8_t v___x_2256_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v___f_2220_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2));
v___x_2256_ = lean_unbox(v_a_2219_);
lean_dec(v_a_2219_);
if (v___x_2256_ == 0)
{
lean_inc(v_fn_2213_);
v___y_2222_ = v_fn_2213_;
goto v___jp_2221_;
}
else
{
lean_object* v___x_2257_; 
lean_inc(v_fn_2213_);
v___x_2257_ = l_Lean_Compiler_LCNF_mkBoxedName(v_fn_2213_);
v___y_2222_ = v___x_2257_;
goto v___jp_2221_;
}
v___jp_2221_:
{
lean_object* v___x_2223_; 
v___x_2223_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2214_, v___f_2220_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v_fst_2225_; lean_object* v_snd_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2223_, 1);
v_fst_2225_ = lean_ctor_get(v_a_2224_, 0);
lean_inc(v_fst_2225_);
v_snd_2226_ = lean_ctor_get(v_a_2224_, 1);
lean_inc(v_snd_2226_);
lean_dec(v_a_2224_);
v___x_2227_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updatePapImp(v___x_1971_, v_value_2024_, v___y_2222_, v_fst_2225_);
v___x_2228_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1971_, v_a_1985_, v___x_2227_, v_a_1951_);
if (lean_obj_tag(v___x_2228_) == 0)
{
if (lean_obj_tag(v_code_1945_) == 0)
{
lean_object* v_a_2229_; lean_object* v_decl_2230_; lean_object* v_k_2231_; size_t v___x_2232_; size_t v___x_2233_; uint8_t v___x_2234_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2228_, 1);
v_decl_2230_ = lean_ctor_get(v_code_1945_, 0);
v_k_2231_ = lean_ctor_get(v_code_1945_, 1);
v___x_2232_ = lean_ptr_addr(v_k_2231_);
v___x_2233_ = lean_ptr_addr(v_a_1990_);
v___x_2234_ = lean_usize_dec_eq(v___x_2232_, v___x_2233_);
if (v___x_2234_ == 0)
{
v___y_1995_ = v_a_2229_;
v___y_1996_ = v_snd_2226_;
v___y_1997_ = v___x_2234_;
goto v___jp_1994_;
}
else
{
size_t v___x_2235_; size_t v___x_2236_; uint8_t v___x_2237_; 
v___x_2235_ = lean_ptr_addr(v_decl_2230_);
v___x_2236_ = lean_ptr_addr(v_a_2229_);
v___x_2237_ = lean_usize_dec_eq(v___x_2235_, v___x_2236_);
v___y_1995_ = v_a_2229_;
v___y_1996_ = v_snd_2226_;
v___y_1997_ = v___x_2237_;
goto v___jp_1994_;
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec_ref_known(v___x_2228_, 1);
lean_dec(v_a_1990_);
lean_dec_ref(v_code_1945_);
v___x_2238_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2239_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2238_);
v___y_1980_ = v_snd_2226_;
v___y_1981_ = v___x_2239_;
goto v___jp_1979_;
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_snd_2226_);
lean_dec(v_a_1990_);
lean_dec_ref(v_code_1945_);
v_a_2240_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2228_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2228_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec(v___y_2222_);
lean_dec(v_a_1990_);
lean_dec(v_a_1985_);
lean_dec_ref(v_code_1945_);
v_a_2248_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2223_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2223_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
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
lean_dec(v_a_1990_);
lean_dec(v_a_1985_);
lean_dec_ref(v_code_1945_);
v_a_2258_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2218_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2218_);
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
lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec(v_a_2216_);
lean_dec(v_a_1990_);
lean_dec(v_a_1985_);
lean_dec_ref(v_code_1945_);
v___x_2266_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4);
v___x_2267_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2266_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
return v___x_2267_;
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec(v_a_1990_);
lean_dec(v_a_1985_);
lean_dec_ref(v_code_1945_);
v_a_2268_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2215_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2215_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
case 11:
{
lean_inc_ref(v_value_2024_);
lean_del_object(v___x_1992_);
lean_del_object(v___x_1969_);
v___y_2026_ = v_a_1951_;
goto v___jp_2025_;
}
case 12:
{
lean_object* v_args_2276_; lean_object* v___f_2277_; lean_object* v___x_2278_; 
lean_del_object(v___x_1992_);
lean_del_object(v___x_1987_);
lean_del_object(v___x_1969_);
lean_dec(v_a_1967_);
v_args_2276_ = lean_ctor_get(v_value_2024_, 2);
v___f_2277_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2));
v___x_2278_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2276_, v___f_2277_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v_fst_2280_; lean_object* v_snd_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2321_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v_fst_2280_ = lean_ctor_get(v_a_2279_, 0);
v_snd_2281_ = lean_ctor_get(v_a_2279_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_a_2279_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2283_ = v_a_2279_;
v_isShared_2284_ = v_isSharedCheck_2321_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_snd_2281_);
lean_inc(v_fst_2280_);
lean_dec(v_a_2279_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2321_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_inc_ref(v_value_2024_);
v___x_2285_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_1971_, v_value_2024_, v_fst_2280_);
v___x_2286_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1971_, v_a_1985_, v___x_2285_, v_a_1951_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2312_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2312_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2312_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___y_2292_; uint8_t v___y_2298_; 
if (lean_obj_tag(v_code_1945_) == 0)
{
lean_object* v_decl_2302_; lean_object* v_k_2303_; size_t v___x_2304_; size_t v___x_2305_; uint8_t v___x_2306_; 
v_decl_2302_ = lean_ctor_get(v_code_1945_, 0);
v_k_2303_ = lean_ctor_get(v_code_1945_, 1);
v___x_2304_ = lean_ptr_addr(v_k_2303_);
v___x_2305_ = lean_ptr_addr(v_a_1990_);
v___x_2306_ = lean_usize_dec_eq(v___x_2304_, v___x_2305_);
if (v___x_2306_ == 0)
{
v___y_2298_ = v___x_2306_;
goto v___jp_2297_;
}
else
{
size_t v___x_2307_; size_t v___x_2308_; uint8_t v___x_2309_; 
v___x_2307_ = lean_ptr_addr(v_decl_2302_);
v___x_2308_ = lean_ptr_addr(v_a_2287_);
v___x_2309_ = lean_usize_dec_eq(v___x_2307_, v___x_2308_);
v___y_2298_ = v___x_2309_;
goto v___jp_2297_;
}
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
lean_dec(v_a_2287_);
lean_del_object(v___x_2283_);
lean_dec(v_a_1990_);
lean_dec_ref(v_code_1945_);
v___x_2310_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2311_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2310_);
v___y_2292_ = v___x_2311_;
goto v___jp_2291_;
}
v___jp_2291_:
{
lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2293_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1971_, v_snd_2281_, v___y_2292_);
lean_dec(v_snd_2281_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v___x_2293_);
v___x_2295_ = v___x_2289_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
v___jp_2297_:
{
if (v___y_2298_ == 0)
{
lean_object* v___x_2300_; 
lean_dec_ref(v_code_1945_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 1, v_a_1990_);
lean_ctor_set(v___x_2283_, 0, v_a_2287_);
v___x_2300_ = v___x_2283_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2287_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_a_1990_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
v___y_2292_ = v___x_2300_;
goto v___jp_2291_;
}
}
else
{
lean_dec(v_a_2287_);
lean_del_object(v___x_2283_);
lean_dec(v_a_1990_);
v___y_2292_ = v_code_1945_;
goto v___jp_2291_;
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_del_object(v___x_2283_);
lean_dec(v_snd_2281_);
lean_dec(v_a_1990_);
lean_dec_ref(v_code_1945_);
v_a_2313_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2286_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2286_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v_a_1990_);
lean_dec(v_a_1985_);
lean_dec_ref(v_code_1945_);
v_a_2322_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2278_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2278_);
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
case 13:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_del_object(v___x_1992_);
lean_dec(v_a_1990_);
lean_del_object(v___x_1987_);
lean_dec(v_a_1985_);
lean_del_object(v___x_1969_);
lean_dec(v_a_1967_);
lean_dec_ref(v_code_1945_);
v___x_2330_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1);
v___x_2331_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2330_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
return v___x_2331_;
}
case 14:
{
lean_del_object(v___x_1992_);
lean_dec(v_a_1990_);
lean_del_object(v___x_1987_);
lean_dec(v_a_1985_);
lean_del_object(v___x_1969_);
lean_dec(v_a_1967_);
lean_dec_ref(v_code_1945_);
v___y_1956_ = v_a_1948_;
v___y_1957_ = v_a_1949_;
v___y_1958_ = v_a_1950_;
v___y_1959_ = v_a_1951_;
v___y_1960_ = v_a_1952_;
v___y_1961_ = v_a_1953_;
goto v___jp_1955_;
}
case 15:
{
lean_del_object(v___x_1992_);
lean_dec(v_a_1990_);
lean_del_object(v___x_1987_);
lean_dec(v_a_1985_);
lean_del_object(v___x_1969_);
lean_dec(v_a_1967_);
lean_dec_ref(v_code_1945_);
v___y_1956_ = v_a_1948_;
v___y_1957_ = v_a_1949_;
v___y_1958_ = v_a_1950_;
v___y_1959_ = v_a_1951_;
v___y_1960_ = v_a_1952_;
v___y_1961_ = v_a_1953_;
goto v___jp_1955_;
}
default: 
{
lean_object* v___x_2332_; 
lean_inc(v_value_2024_);
lean_del_object(v___x_1992_);
lean_del_object(v___x_1987_);
lean_del_object(v___x_1969_);
v___x_2332_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_1971_, v_a_1985_, v_a_1967_, v_value_2024_, v_a_1951_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2357_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2357_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2357_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
uint8_t v___y_2338_; 
if (lean_obj_tag(v_code_1945_) == 0)
{
lean_object* v_decl_2346_; lean_object* v_k_2347_; size_t v___x_2348_; size_t v___x_2349_; uint8_t v___x_2350_; 
v_decl_2346_ = lean_ctor_get(v_code_1945_, 0);
v_k_2347_ = lean_ctor_get(v_code_1945_, 1);
v___x_2348_ = lean_ptr_addr(v_k_2347_);
v___x_2349_ = lean_ptr_addr(v_a_1990_);
v___x_2350_ = lean_usize_dec_eq(v___x_2348_, v___x_2349_);
if (v___x_2350_ == 0)
{
v___y_2338_ = v___x_2350_;
goto v___jp_2337_;
}
else
{
size_t v___x_2351_; size_t v___x_2352_; uint8_t v___x_2353_; 
v___x_2351_ = lean_ptr_addr(v_decl_2346_);
v___x_2352_ = lean_ptr_addr(v_a_2333_);
v___x_2353_ = lean_usize_dec_eq(v___x_2351_, v___x_2352_);
v___y_2338_ = v___x_2353_;
goto v___jp_2337_;
}
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_del_object(v___x_2335_);
lean_dec(v_a_2333_);
lean_dec(v_a_1990_);
lean_dec_ref(v_code_1945_);
v___x_2354_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2355_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2354_);
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
return v___x_2356_;
}
v___jp_2337_:
{
if (v___y_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
lean_dec_ref(v_code_1945_);
v___x_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2339_, 0, v_a_2333_);
lean_ctor_set(v___x_2339_, 1, v_a_1990_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2339_);
v___x_2341_ = v___x_2335_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
else
{
lean_object* v___x_2344_; 
lean_dec(v_a_2333_);
lean_dec(v_a_1990_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v_code_1945_);
v___x_2344_ = v___x_2335_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_code_1945_);
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
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v_a_1990_);
lean_dec_ref(v_code_1945_);
v_a_2358_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2332_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2332_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
v___jp_1994_:
{
if (v___y_1997_ == 0)
{
lean_object* v___x_1998_; 
lean_dec_ref(v_code_1945_);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___y_1995_);
lean_ctor_set(v___x_1998_, 1, v_a_1990_);
v___y_1980_ = v___y_1996_;
v___y_1981_ = v___x_1998_;
goto v___jp_1979_;
}
else
{
lean_dec_ref(v___y_1995_);
lean_dec(v_a_1990_);
v___y_1980_ = v___y_1996_;
v___y_1981_ = v_code_1945_;
goto v___jp_1979_;
}
}
v___jp_1999_:
{
if (v___y_2002_ == 0)
{
lean_object* v___x_2003_; 
lean_dec_ref(v_code_1945_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___y_2001_);
lean_ctor_set(v___x_2003_, 1, v_a_1990_);
v___y_1973_ = v___y_2000_;
v___y_1974_ = v___x_2003_;
goto v___jp_1972_;
}
else
{
lean_dec_ref(v___y_2001_);
lean_dec(v_a_1990_);
v___y_1973_ = v___y_2000_;
v___y_1974_ = v_code_1945_;
goto v___jp_1972_;
}
}
v___jp_2004_:
{
if (v___y_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
lean_dec_ref(v_code_1945_);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___y_2005_);
lean_ctor_set(v___x_2007_, 1, v_a_1990_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_2007_);
v___x_2009_ = v___x_1992_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
else
{
lean_object* v___x_2012_; 
lean_dec_ref(v___y_2005_);
lean_dec(v_a_1990_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v_code_1945_);
v___x_2012_ = v___x_1992_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_code_1945_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
v___jp_2014_:
{
if (v___y_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
lean_dec_ref(v_code_1945_);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___y_2015_);
lean_ctor_set(v___x_2017_, 1, v_a_1990_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v___x_2017_);
v___x_2019_ = v___x_1987_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
else
{
lean_object* v___x_2022_; 
lean_dec_ref(v___y_2015_);
lean_dec(v_a_1990_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v_code_1945_);
v___x_2022_ = v___x_1987_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_code_1945_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
v___jp_2025_:
{
lean_object* v___x_2027_; 
v___x_2027_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_1971_, v_a_1985_, v_a_1967_, v_value_2024_, v___y_2026_);
if (lean_obj_tag(v___x_2027_) == 0)
{
if (lean_obj_tag(v_code_1945_) == 0)
{
lean_object* v_a_2028_; lean_object* v_decl_2029_; lean_object* v_k_2030_; size_t v___x_2031_; size_t v___x_2032_; uint8_t v___x_2033_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
v_decl_2029_ = lean_ctor_get(v_code_1945_, 0);
v_k_2030_ = lean_ctor_get(v_code_1945_, 1);
v___x_2031_ = lean_ptr_addr(v_k_2030_);
v___x_2032_ = lean_ptr_addr(v_a_1990_);
v___x_2033_ = lean_usize_dec_eq(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
v___y_2015_ = v_a_2028_;
v___y_2016_ = v___x_2033_;
goto v___jp_2014_;
}
else
{
size_t v___x_2034_; size_t v___x_2035_; uint8_t v___x_2036_; 
v___x_2034_ = lean_ptr_addr(v_decl_2029_);
v___x_2035_ = lean_ptr_addr(v_a_2028_);
v___x_2036_ = lean_usize_dec_eq(v___x_2034_, v___x_2035_);
v___y_2015_ = v_a_2028_;
v___y_2016_ = v___x_2036_;
goto v___jp_2014_;
}
}
else
{
lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_a_1990_);
lean_del_object(v___x_1987_);
lean_dec_ref(v_code_1945_);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v___x_2027_, 0);
lean_dec(v_unused_2046_);
v___x_2038_ = v___x_2027_;
v_isShared_2039_ = v_isSharedCheck_2045_;
goto v_resetjp_2037_;
}
else
{
lean_dec(v___x_2027_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2045_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2043_; 
v___x_2040_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2041_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2040_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2041_);
v___x_2043_ = v___x_2038_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2041_);
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
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_a_1990_);
lean_del_object(v___x_1987_);
lean_dec_ref(v_code_1945_);
v_a_2047_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2027_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2027_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1987_);
lean_dec(v_a_1985_);
lean_del_object(v___x_1969_);
lean_dec(v_a_1967_);
lean_dec_ref(v_code_1945_);
return v___x_1989_;
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_del_object(v___x_1969_);
lean_dec(v_a_1967_);
lean_dec_ref(v_k_1947_);
lean_dec_ref(v_code_1945_);
v_a_2368_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_1984_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_1984_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
v___jp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1975_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1971_, v___y_1973_, v___y_1974_);
lean_dec_ref(v___y_1973_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1975_);
v___x_1977_ = v___x_1969_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
v___jp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1971_, v___y_1980_, v___y_1981_);
lean_dec_ref(v___y_1980_);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_value_1965_);
lean_dec_ref(v_k_1947_);
lean_dec_ref(v_decl_1946_);
lean_dec_ref(v_code_1945_);
v_a_2377_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_1966_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_1966_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
v___jp_1955_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1);
v___x_1963_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_1962_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
return v___x_1963_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2386_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_2387_ = lean_unsigned_to_nat(44u);
v___x_2388_ = lean_unsigned_to_nat(284u);
v___x_2389_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0));
v___x_2390_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_2391_ = l_mkPanicMessageWithDecl(v___x_2390_, v___x_2389_, v___x_2388_, v___x_2387_, v___x_2386_);
return v___x_2391_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2392_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_2393_ = lean_unsigned_to_nat(59u);
v___x_2394_ = lean_unsigned_to_nat(287u);
v___x_2395_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0));
v___x_2396_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_2397_ = l_mkPanicMessageWithDecl(v___x_2396_, v___x_2395_, v___x_2394_, v___x_2393_, v___x_2392_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(lean_object* v_code_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
switch(lean_obj_tag(v_code_2398_))
{
case 0:
{
lean_object* v_decl_2406_; lean_object* v_k_2407_; lean_object* v___x_2408_; 
v_decl_2406_ = lean_ctor_get(v_code_2398_, 0);
lean_inc_ref(v_decl_2406_);
v_k_2407_ = lean_ctor_get(v_code_2398_, 1);
lean_inc_ref(v_k_2407_);
v___x_2408_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(v_code_2398_, v_decl_2406_, v_k_2407_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
return v___x_2408_;
}
case 2:
{
lean_object* v_decl_2409_; lean_object* v_k_2410_; lean_object* v_params_2411_; lean_object* v_value_2412_; lean_object* v___x_2413_; 
v_decl_2409_ = lean_ctor_get(v_code_2398_, 0);
v_k_2410_ = lean_ctor_get(v_code_2398_, 1);
v_params_2411_ = lean_ctor_get(v_decl_2409_, 2);
v_value_2412_ = lean_ctor_get(v_decl_2409_, 4);
lean_inc_ref(v_value_2412_);
v___x_2413_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_value_2412_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v_currDeclResultType_2415_; uint8_t v___x_2416_; lean_object* v___x_2417_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2413_, 1);
v_currDeclResultType_2415_ = lean_ctor_get(v_a_2399_, 1);
v___x_2416_ = 1;
lean_inc_ref(v_params_2411_);
lean_inc_ref(v_currDeclResultType_2415_);
lean_inc_ref(v_decl_2409_);
v___x_2417_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2416_, v_decl_2409_, v_currDeclResultType_2415_, v_params_2411_, v_a_2414_, v_a_2402_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2419_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
lean_inc_ref(v_k_2410_);
v___x_2419_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2410_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2447_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2447_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2447_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
uint8_t v___y_2425_; size_t v___x_2441_; size_t v___x_2442_; uint8_t v___x_2443_; 
v___x_2441_ = lean_ptr_addr(v_k_2410_);
v___x_2442_ = lean_ptr_addr(v_a_2420_);
v___x_2443_ = lean_usize_dec_eq(v___x_2441_, v___x_2442_);
if (v___x_2443_ == 0)
{
v___y_2425_ = v___x_2443_;
goto v___jp_2424_;
}
else
{
size_t v___x_2444_; size_t v___x_2445_; uint8_t v___x_2446_; 
v___x_2444_ = lean_ptr_addr(v_decl_2409_);
v___x_2445_ = lean_ptr_addr(v_a_2418_);
v___x_2446_ = lean_usize_dec_eq(v___x_2444_, v___x_2445_);
v___y_2425_ = v___x_2446_;
goto v___jp_2424_;
}
v___jp_2424_:
{
if (v___y_2425_ == 0)
{
lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2435_; 
v_isSharedCheck_2435_ = !lean_is_exclusive(v_code_2398_);
if (v_isSharedCheck_2435_ == 0)
{
lean_object* v_unused_2436_; lean_object* v_unused_2437_; 
v_unused_2436_ = lean_ctor_get(v_code_2398_, 1);
lean_dec(v_unused_2436_);
v_unused_2437_ = lean_ctor_get(v_code_2398_, 0);
lean_dec(v_unused_2437_);
v___x_2427_ = v_code_2398_;
v_isShared_2428_ = v_isSharedCheck_2435_;
goto v_resetjp_2426_;
}
else
{
lean_dec(v_code_2398_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2435_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 1, v_a_2420_);
lean_ctor_set(v___x_2427_, 0, v_a_2418_);
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2418_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_a_2420_);
v___x_2430_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
lean_object* v___x_2432_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2430_);
v___x_2432_ = v___x_2422_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
else
{
lean_object* v___x_2439_; 
lean_dec(v_a_2420_);
lean_dec(v_a_2418_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v_code_2398_);
v___x_2439_ = v___x_2422_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_code_2398_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
}
else
{
lean_dec(v_a_2418_);
lean_dec_ref_known(v_code_2398_, 2);
return v___x_2419_;
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec_ref_known(v_code_2398_, 2);
v_a_2448_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2417_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2417_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_2398_, 2);
return v___x_2413_;
}
}
case 3:
{
lean_object* v_fvarId_2456_; lean_object* v_args_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; 
v_fvarId_2456_ = lean_ctor_get(v_code_2398_, 0);
v_args_2457_ = lean_ctor_get(v_code_2398_, 1);
v___x_2458_ = 1;
v___x_2459_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_2458_, v_fvarId_2456_, v_a_2402_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2459_, 1);
if (lean_obj_tag(v_a_2460_) == 1)
{
lean_object* v_val_2461_; lean_object* v_params_2462_; lean_object* v___x_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; 
v_val_2461_ = lean_ctor_get(v_a_2460_, 0);
lean_inc(v_val_2461_);
lean_dec_ref_known(v_a_2460_, 1);
v_params_2462_ = lean_ctor_get(v_val_2461_, 2);
lean_inc_ref(v_params_2462_);
lean_dec(v_val_2461_);
v___x_2463_ = lean_box(v___x_2458_);
v___f_2464_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2464_, 0, v___x_2463_);
lean_closure_set(v___f_2464_, 1, v_params_2462_);
v___x_2465_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2457_, v___f_2464_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2493_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2493_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2493_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v_fst_2470_; lean_object* v_snd_2471_; lean_object* v___y_2473_; uint8_t v___y_2479_; uint8_t v___x_2489_; 
v_fst_2470_ = lean_ctor_get(v_a_2466_, 0);
lean_inc(v_fst_2470_);
v_snd_2471_ = lean_ctor_get(v_a_2466_, 1);
lean_inc(v_snd_2471_);
lean_dec(v_a_2466_);
v___x_2489_ = l_Lean_instBEqFVarId_beq(v_fvarId_2456_, v_fvarId_2456_);
if (v___x_2489_ == 0)
{
v___y_2479_ = v___x_2489_;
goto v___jp_2478_;
}
else
{
size_t v___x_2490_; size_t v___x_2491_; uint8_t v___x_2492_; 
v___x_2490_ = lean_ptr_addr(v_args_2457_);
v___x_2491_ = lean_ptr_addr(v_fst_2470_);
v___x_2492_ = lean_usize_dec_eq(v___x_2490_, v___x_2491_);
v___y_2479_ = v___x_2492_;
goto v___jp_2478_;
}
v___jp_2472_:
{
lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2474_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2458_, v_snd_2471_, v___y_2473_);
lean_dec(v_snd_2471_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2474_);
v___x_2476_ = v___x_2468_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
v___jp_2478_:
{
if (v___y_2479_ == 0)
{
lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_inc(v_fvarId_2456_);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_code_2398_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; lean_object* v_unused_2488_; 
v_unused_2487_ = lean_ctor_get(v_code_2398_, 1);
lean_dec(v_unused_2487_);
v_unused_2488_ = lean_ctor_get(v_code_2398_, 0);
lean_dec(v_unused_2488_);
v___x_2481_ = v_code_2398_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_dec(v_code_2398_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 1, v_fst_2470_);
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_fvarId_2456_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_fst_2470_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
v___y_2473_ = v___x_2484_;
goto v___jp_2472_;
}
}
}
else
{
lean_dec(v_fst_2470_);
v___y_2473_ = v_code_2398_;
goto v___jp_2472_;
}
}
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec_ref_known(v_code_2398_, 2);
v_a_2494_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2465_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2465_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
else
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_dec(v_a_2460_);
lean_dec_ref_known(v_code_2398_, 2);
v___x_2502_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1);
v___x_2503_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2502_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
return v___x_2503_;
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec_ref_known(v_code_2398_, 2);
v_a_2504_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2459_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2459_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
case 4:
{
lean_object* v_cases_2512_; lean_object* v_typeName_2513_; lean_object* v_resultType_2514_; lean_object* v_discr_2515_; lean_object* v_alts_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v_cases_2512_ = lean_ctor_get(v_code_2398_, 0);
v_typeName_2513_ = lean_ctor_get(v_cases_2512_, 0);
lean_inc(v_typeName_2513_);
v_resultType_2514_ = lean_ctor_get(v_cases_2512_, 1);
lean_inc_ref(v_resultType_2514_);
v_discr_2515_ = lean_ctor_get(v_cases_2512_, 2);
lean_inc(v_discr_2515_);
v_alts_2516_ = lean_ctor_get(v_cases_2512_, 3);
lean_inc_ref_n(v_alts_2516_, 2);
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(v___x_2517_, v_alts_2516_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2520_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2518_, 1);
lean_inc(v_discr_2515_);
v___x_2520_ = l_Lean_Compiler_LCNF_getType(v_discr_2515_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v___x_2522_ = lean_box(0);
lean_inc(v_typeName_2513_);
v___x_2523_ = l_Lean_mkConst(v_typeName_2513_, v___x_2522_);
v___x_2524_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2521_, v___x_2523_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; 
lean_inc_ref(v___x_2523_);
lean_inc(v_discr_2515_);
v___x_2525_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_discr_2515_, v_a_2521_, v___x_2523_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; uint8_t v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v___x_2527_ = 1;
v___x_2528_ = lean_box(0);
v___x_2529_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2527_, v___x_2528_, v___x_2523_, v_a_2526_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v_fvarId_2531_; lean_object* v___x_2532_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v___x_2529_, 1);
v_fvarId_2531_ = lean_ctor_get(v_a_2530_, 0);
lean_inc(v_fvarId_2531_);
v___x_2532_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_2513_, v_a_2519_, v_discr_2515_, v_code_2398_, v_alts_2516_, v_resultType_2514_, v_fvarId_2531_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec_ref(v_resultType_2514_);
lean_dec_ref(v_alts_2516_);
lean_dec(v_discr_2515_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2541_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2541_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2541_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; lean_object* v___x_2539_; 
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v_a_2530_);
lean_ctor_set(v___x_2537_, 1, v_a_2533_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2537_);
v___x_2539_ = v___x_2535_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
else
{
lean_dec(v_a_2530_);
return v___x_2532_;
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_a_2519_);
lean_dec_ref(v_alts_2516_);
lean_dec(v_discr_2515_);
lean_dec_ref(v_resultType_2514_);
lean_dec(v_typeName_2513_);
lean_dec_ref_known(v_code_2398_, 1);
v_a_2542_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2529_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2529_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_dec_ref(v___x_2523_);
lean_dec(v_a_2519_);
lean_dec_ref(v_alts_2516_);
lean_dec(v_discr_2515_);
lean_dec_ref(v_resultType_2514_);
lean_dec(v_typeName_2513_);
lean_dec_ref_known(v_code_2398_, 1);
v_a_2550_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2525_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2525_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
else
{
lean_object* v___x_2558_; 
lean_dec_ref(v___x_2523_);
lean_dec(v_a_2521_);
lean_inc(v_discr_2515_);
v___x_2558_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_2513_, v_a_2519_, v_discr_2515_, v_code_2398_, v_alts_2516_, v_resultType_2514_, v_discr_2515_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec_ref(v_resultType_2514_);
lean_dec_ref(v_alts_2516_);
lean_dec(v_discr_2515_);
return v___x_2558_;
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec(v_a_2519_);
lean_dec_ref(v_alts_2516_);
lean_dec(v_discr_2515_);
lean_dec_ref(v_resultType_2514_);
lean_dec(v_typeName_2513_);
lean_dec_ref_known(v_code_2398_, 1);
v_a_2559_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2520_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2520_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec_ref(v_alts_2516_);
lean_dec(v_discr_2515_);
lean_dec_ref(v_resultType_2514_);
lean_dec(v_typeName_2513_);
lean_dec_ref_known(v_code_2398_, 1);
v_a_2567_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2518_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2518_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_2575_; lean_object* v___x_2576_; 
v_fvarId_2575_ = lean_ctor_get(v_code_2398_, 0);
lean_inc_n(v_fvarId_2575_, 2);
v___x_2576_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2575_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v_currDeclResultType_2578_; uint8_t v___x_2579_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___x_2576_, 1);
v_currDeclResultType_2578_ = lean_ctor_get(v_a_2399_, 1);
v___x_2579_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2577_, v_currDeclResultType_2578_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; 
lean_inc_ref(v_currDeclResultType_2578_);
lean_inc(v_fvarId_2575_);
v___x_2580_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_2575_, v_a_2577_, v_currDeclResultType_2578_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; uint8_t v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2580_, 1);
v___x_2582_ = 1;
v___x_2583_ = lean_box(0);
lean_inc_ref(v_currDeclResultType_2578_);
v___x_2584_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2582_, v___x_2583_, v_currDeclResultType_2578_, v_a_2581_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v_fvarId_2586_; lean_object* v___x_2587_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v_fvarId_2586_ = lean_ctor_get(v_a_2585_, 0);
lean_inc(v_fvarId_2586_);
v___x_2587_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_2575_, v_code_2398_, v_fvarId_2586_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec(v_fvarId_2575_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2596_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2596_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2596_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2592_, 0, v_a_2585_);
lean_ctor_set(v___x_2592_, 1, v_a_2588_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2592_);
v___x_2594_ = v___x_2590_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
else
{
lean_dec(v_a_2585_);
return v___x_2587_;
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec(v_fvarId_2575_);
lean_dec_ref_known(v_code_2398_, 1);
v_a_2597_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2584_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2584_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec(v_fvarId_2575_);
lean_dec_ref_known(v_code_2398_, 1);
v_a_2605_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2580_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2580_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v___x_2613_; 
lean_dec(v_a_2577_);
lean_inc(v_fvarId_2575_);
v___x_2613_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_2575_, v_code_2398_, v_fvarId_2575_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec(v_fvarId_2575_);
return v___x_2613_;
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v_fvarId_2575_);
lean_dec_ref_known(v_code_2398_, 1);
v_a_2614_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2576_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2576_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
case 6:
{
lean_object* v_type_2622_; lean_object* v_currDeclResultType_2623_; size_t v___x_2624_; size_t v___x_2625_; uint8_t v___x_2626_; 
v_type_2622_ = lean_ctor_get(v_code_2398_, 0);
v_currDeclResultType_2623_ = lean_ctor_get(v_a_2399_, 1);
v___x_2624_ = lean_ptr_addr(v_type_2622_);
v___x_2625_ = lean_ptr_addr(v_currDeclResultType_2623_);
v___x_2626_ = lean_usize_dec_eq(v___x_2624_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2634_; 
v_isSharedCheck_2634_ = !lean_is_exclusive(v_code_2398_);
if (v_isSharedCheck_2634_ == 0)
{
lean_object* v_unused_2635_; 
v_unused_2635_ = lean_ctor_get(v_code_2398_, 0);
lean_dec(v_unused_2635_);
v___x_2628_ = v_code_2398_;
v_isShared_2629_ = v_isSharedCheck_2634_;
goto v_resetjp_2627_;
}
else
{
lean_dec(v_code_2398_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2634_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
lean_inc_ref(v_currDeclResultType_2623_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v_currDeclResultType_2623_);
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_currDeclResultType_2623_);
v___x_2631_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
return v___x_2632_;
}
}
}
else
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v_code_2398_);
return v___x_2636_;
}
}
case 8:
{
lean_object* v_fvarId_2637_; lean_object* v_i_2638_; lean_object* v_y_2639_; lean_object* v_k_2640_; lean_object* v___x_2641_; 
v_fvarId_2637_ = lean_ctor_get(v_code_2398_, 0);
lean_inc(v_fvarId_2637_);
v_i_2638_ = lean_ctor_get(v_code_2398_, 1);
lean_inc(v_i_2638_);
v_y_2639_ = lean_ctor_get(v_code_2398_, 2);
lean_inc(v_y_2639_);
v_k_2640_ = lean_ctor_get(v_code_2398_, 3);
lean_inc_ref_n(v_k_2640_, 2);
v___x_2641_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2640_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2643_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
lean_inc(v_y_2639_);
v___x_2643_ = l_Lean_Compiler_LCNF_getType(v_y_2639_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2645_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11);
v___x_2646_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2644_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; 
lean_inc(v_y_2639_);
v___x_2647_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_y_2639_, v_a_2644_, v___x_2645_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; uint8_t v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v___x_2649_ = 1;
v___x_2650_ = lean_box(0);
v___x_2651_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2649_, v___x_2650_, v___x_2645_, v_a_2648_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v_fvarId_2653_; lean_object* v___x_2654_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
v_fvarId_2653_ = lean_ctor_get(v_a_2652_, 0);
lean_inc(v_fvarId_2653_);
v___x_2654_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_2637_, v_i_2638_, v_a_2642_, v_y_2639_, v_k_2640_, v_code_2398_, v_fvarId_2653_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec_ref(v_k_2640_);
lean_dec(v_y_2639_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2663_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2657_ = v___x_2654_;
v_isShared_2658_ = v_isSharedCheck_2663_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2654_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2663_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2659_, 0, v_a_2652_);
lean_ctor_set(v___x_2659_, 1, v_a_2655_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2659_);
v___x_2661_ = v___x_2657_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
else
{
lean_dec(v_a_2652_);
return v___x_2654_;
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec(v_a_2642_);
lean_dec_ref(v_k_2640_);
lean_dec(v_y_2639_);
lean_dec(v_i_2638_);
lean_dec(v_fvarId_2637_);
lean_dec_ref_known(v_code_2398_, 4);
v_a_2664_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2651_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2651_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec(v_a_2642_);
lean_dec_ref(v_k_2640_);
lean_dec(v_y_2639_);
lean_dec(v_i_2638_);
lean_dec(v_fvarId_2637_);
lean_dec_ref_known(v_code_2398_, 4);
v_a_2672_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2647_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2647_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
else
{
lean_object* v___x_2680_; 
lean_dec(v_a_2644_);
lean_inc(v_y_2639_);
v___x_2680_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_2637_, v_i_2638_, v_a_2642_, v_y_2639_, v_k_2640_, v_code_2398_, v_y_2639_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec_ref(v_k_2640_);
lean_dec(v_y_2639_);
return v___x_2680_;
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec(v_a_2642_);
lean_dec_ref(v_k_2640_);
lean_dec(v_y_2639_);
lean_dec(v_i_2638_);
lean_dec(v_fvarId_2637_);
lean_dec_ref_known(v_code_2398_, 4);
v_a_2681_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2643_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2643_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
else
{
lean_dec_ref(v_k_2640_);
lean_dec(v_y_2639_);
lean_dec(v_i_2638_);
lean_dec(v_fvarId_2637_);
lean_dec_ref_known(v_code_2398_, 4);
return v___x_2641_;
}
}
case 9:
{
lean_object* v_fvarId_2689_; lean_object* v_i_2690_; lean_object* v_offset_2691_; lean_object* v_y_2692_; lean_object* v_ty_2693_; lean_object* v_k_2694_; lean_object* v___x_2695_; 
v_fvarId_2689_ = lean_ctor_get(v_code_2398_, 0);
lean_inc(v_fvarId_2689_);
v_i_2690_ = lean_ctor_get(v_code_2398_, 1);
lean_inc(v_i_2690_);
v_offset_2691_ = lean_ctor_get(v_code_2398_, 2);
lean_inc(v_offset_2691_);
v_y_2692_ = lean_ctor_get(v_code_2398_, 3);
lean_inc(v_y_2692_);
v_ty_2693_ = lean_ctor_get(v_code_2398_, 4);
lean_inc_ref(v_ty_2693_);
v_k_2694_ = lean_ctor_get(v_code_2398_, 5);
lean_inc_ref_n(v_k_2694_, 2);
v___x_2695_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2694_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
lean_inc(v_y_2692_);
v___x_2697_ = l_Lean_Compiler_LCNF_getType(v_y_2692_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; uint8_t v___x_2699_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2699_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2698_, v_ty_2693_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; 
lean_inc_ref(v_ty_2693_);
lean_inc(v_y_2692_);
v___x_2700_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_y_2692_, v_a_2698_, v_ty_2693_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; uint8_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
lean_dec_ref_known(v___x_2700_, 1);
v___x_2702_ = 1;
v___x_2703_ = lean_box(0);
lean_inc_ref(v_ty_2693_);
v___x_2704_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2702_, v___x_2703_, v_ty_2693_, v_a_2701_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v_fvarId_2706_; lean_object* v___x_2707_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2704_, 1);
v_fvarId_2706_ = lean_ctor_get(v_a_2705_, 0);
lean_inc(v_fvarId_2706_);
v___x_2707_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_2689_, v_i_2690_, v_offset_2691_, v_ty_2693_, v_a_2696_, v_y_2692_, v_k_2694_, v_code_2398_, v_fvarId_2706_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec_ref(v_k_2694_);
lean_dec(v_y_2692_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2716_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2716_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2716_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v___x_2714_; 
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v_a_2705_);
lean_ctor_set(v___x_2712_, 1, v_a_2708_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2712_);
v___x_2714_ = v___x_2710_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
else
{
lean_dec(v_a_2705_);
return v___x_2707_;
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v_a_2696_);
lean_dec_ref(v_k_2694_);
lean_dec_ref(v_ty_2693_);
lean_dec(v_y_2692_);
lean_dec(v_offset_2691_);
lean_dec(v_i_2690_);
lean_dec(v_fvarId_2689_);
lean_dec_ref_known(v_code_2398_, 6);
v_a_2717_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2704_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2704_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v_a_2696_);
lean_dec_ref(v_k_2694_);
lean_dec_ref(v_ty_2693_);
lean_dec(v_y_2692_);
lean_dec(v_offset_2691_);
lean_dec(v_i_2690_);
lean_dec(v_fvarId_2689_);
lean_dec_ref_known(v_code_2398_, 6);
v_a_2725_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2700_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2700_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
else
{
lean_object* v___x_2733_; 
lean_dec(v_a_2698_);
lean_inc(v_y_2692_);
v___x_2733_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_2689_, v_i_2690_, v_offset_2691_, v_ty_2693_, v_a_2696_, v_y_2692_, v_k_2694_, v_code_2398_, v_y_2692_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec_ref(v_k_2694_);
lean_dec(v_y_2692_);
return v___x_2733_;
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_a_2696_);
lean_dec_ref(v_k_2694_);
lean_dec_ref(v_ty_2693_);
lean_dec(v_y_2692_);
lean_dec(v_offset_2691_);
lean_dec(v_i_2690_);
lean_dec(v_fvarId_2689_);
lean_dec_ref_known(v_code_2398_, 6);
v_a_2734_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2697_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2697_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_dec_ref(v_k_2694_);
lean_dec_ref(v_ty_2693_);
lean_dec(v_y_2692_);
lean_dec(v_offset_2691_);
lean_dec(v_i_2690_);
lean_dec(v_fvarId_2689_);
lean_dec_ref_known(v_code_2398_, 6);
return v___x_2695_;
}
}
default: 
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
lean_dec_ref(v_code_2398_);
v___x_2742_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2);
v___x_2743_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2742_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
return v___x_2743_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed(lean_object* v_code_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_code_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(lean_object* v_i_2753_, lean_object* v_as_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___x_2762_; uint8_t v___x_2763_; 
v___x_2762_ = lean_array_get_size(v_as_2754_);
v___x_2763_ = lean_nat_dec_lt(v_i_2753_, v___x_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; 
lean_dec(v_i_2753_);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v_as_2754_);
return v___x_2764_;
}
else
{
lean_object* v___f_2765_; lean_object* v_a_2766_; lean_object* v___x_2767_; 
v___f_2765_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed), 8, 0);
v_a_2766_ = lean_array_fget_borrowed(v_as_2754_, v_i_2753_);
lean_inc(v_a_2766_);
v___x_2767_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_a_2766_, v___f_2765_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; size_t v___x_2769_; size_t v___x_2770_; uint8_t v___x_2771_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2769_ = lean_ptr_addr(v_a_2766_);
v___x_2770_ = lean_ptr_addr(v_a_2768_);
v___x_2771_ = lean_usize_dec_eq(v___x_2769_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = lean_unsigned_to_nat(1u);
v___x_2773_ = lean_nat_add(v_i_2753_, v___x_2772_);
v___x_2774_ = lean_array_fset(v_as_2754_, v_i_2753_, v_a_2768_);
lean_dec(v_i_2753_);
v_i_2753_ = v___x_2773_;
v_as_2754_ = v___x_2774_;
goto _start;
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
lean_dec(v_a_2768_);
v___x_2776_ = lean_unsigned_to_nat(1u);
v___x_2777_ = lean_nat_add(v_i_2753_, v___x_2776_);
lean_dec(v_i_2753_);
v_i_2753_ = v___x_2777_;
goto _start;
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec_ref(v_as_2754_);
lean_dec(v_i_2753_);
v_a_2779_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2767_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2767_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3___boxed(lean_object* v_i_2787_, lean_object* v_as_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(v_i_2787_, v_as_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___boxed(lean_object* v_code_2797_, lean_object* v_decl_2798_, lean_object* v_k_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(v_code_2797_, v_decl_2798_, v_k_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(uint8_t v_pu_2808_, lean_object* v_alt_2809_, lean_object* v_f_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_alt_2809_, v_f_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___boxed(lean_object* v_pu_2819_, lean_object* v_alt_2820_, lean_object* v_f_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
uint8_t v_pu_boxed_2829_; lean_object* v_res_2830_; 
v_pu_boxed_2829_ = lean_unbox(v_pu_2819_);
v_res_2830_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(v_pu_boxed_2829_, v_alt_2820_, v_f_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(lean_object* v_as_2834_, size_t v_i_2835_, size_t v_stop_2836_, lean_object* v_b_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_a_2844_; uint8_t v___x_2848_; 
v___x_2848_ = lean_usize_dec_eq(v_i_2835_, v_stop_2836_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; lean_object* v_value_2850_; 
v___x_2849_ = lean_array_uget(v_as_2834_, v_i_2835_);
v_value_2850_ = lean_ctor_get(v___x_2849_, 1);
lean_inc_ref(v_value_2850_);
if (lean_obj_tag(v_value_2850_) == 0)
{
lean_object* v_toSignature_2851_; uint8_t v_recursive_2852_; lean_object* v_inlineAttr_x3f_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2898_; 
v_toSignature_2851_ = lean_ctor_get(v___x_2849_, 0);
v_recursive_2852_ = lean_ctor_get_uint8(v___x_2849_, sizeof(void*)*3);
v_inlineAttr_x3f_2853_ = lean_ctor_get(v___x_2849_, 2);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v___x_2849_, 1);
lean_dec(v_unused_2899_);
v___x_2855_ = v___x_2849_;
v_isShared_2856_ = v_isSharedCheck_2898_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_inlineAttr_x3f_2853_);
lean_inc(v_toSignature_2851_);
lean_dec(v___x_2849_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2898_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v_code_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2897_; 
v_code_2857_ = lean_ctor_get(v_value_2850_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_value_2850_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2859_ = v_value_2850_;
v_isShared_2860_ = v_isSharedCheck_2897_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_code_2857_);
lean_dec(v_value_2850_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2897_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v_name_2863_; lean_object* v_type_2864_; lean_object* v_s_2865_; lean_object* v___x_2866_; 
v___x_2861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0));
v___x_2862_ = lean_st_mk_ref(v___x_2861_);
v_name_2863_ = lean_ctor_get(v_toSignature_2851_, 0);
v_type_2864_ = lean_ctor_get(v_toSignature_2851_, 2);
lean_inc_ref(v_type_2864_);
lean_inc(v_name_2863_);
v_s_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_2865_, 0, v_name_2863_);
lean_ctor_set(v_s_2865_, 1, v_type_2864_);
v___x_2866_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_code_2857_, v_s_2865_, v___x_2862_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec_ref_known(v_s_2865_, 2);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; lean_object* v___x_2871_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2866_, 1);
v___x_2868_ = lean_st_ref_get(v___x_2862_);
lean_dec(v___x_2862_);
v___x_2869_ = 1;
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v_a_2867_);
v___x_2871_ = v___x_2859_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2867_);
v___x_2871_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2873_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 1, v___x_2871_);
v___x_2873_ = v___x_2855_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_toSignature_2851_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v___x_2871_);
lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_inlineAttr_x3f_2853_);
lean_ctor_set_uint8(v_reuseFailAlloc_2887_, sizeof(void*)*3, v_recursive_2852_);
v___x_2873_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_2869_, v___x_2873_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v_auxDecls_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v_auxDecls_2876_ = lean_ctor_get(v___x_2868_, 0);
lean_inc_ref(v_auxDecls_2876_);
lean_dec(v___x_2868_);
v___x_2877_ = l_Array_append___redArg(v_b_2837_, v_auxDecls_2876_);
lean_dec_ref(v_auxDecls_2876_);
v___x_2878_ = lean_array_push(v___x_2877_, v_a_2875_);
v_a_2844_ = v___x_2878_;
goto v___jp_2843_;
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v___x_2868_);
lean_dec_ref(v_b_2837_);
v_a_2879_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2874_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2874_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec(v___x_2862_);
lean_del_object(v___x_2859_);
lean_del_object(v___x_2855_);
lean_dec(v_inlineAttr_x3f_2853_);
lean_dec_ref(v_toSignature_2851_);
lean_dec_ref(v_b_2837_);
v_a_2889_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2866_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2866_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
}
else
{
lean_object* v___x_2900_; 
lean_dec_ref_known(v_value_2850_, 1);
v___x_2900_ = lean_array_push(v_b_2837_, v___x_2849_);
v_a_2844_ = v___x_2900_;
goto v___jp_2843_;
}
}
else
{
lean_object* v___x_2901_; 
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v_b_2837_);
return v___x_2901_;
}
v___jp_2843_:
{
size_t v___x_2845_; size_t v___x_2846_; 
v___x_2845_ = ((size_t)1ULL);
v___x_2846_ = lean_usize_add(v_i_2835_, v___x_2845_);
v_i_2835_ = v___x_2846_;
v_b_2837_ = v_a_2844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___boxed(lean_object* v_as_2902_, lean_object* v_i_2903_, lean_object* v_stop_2904_, lean_object* v_b_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
size_t v_i_boxed_2911_; size_t v_stop_boxed_2912_; lean_object* v_res_2913_; 
v_i_boxed_2911_ = lean_unbox_usize(v_i_2903_);
lean_dec(v_i_2903_);
v_stop_boxed_2912_ = lean_unbox_usize(v_stop_2904_);
lean_dec(v_stop_2904_);
v_res_2913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_as_2902_, v_i_boxed_2911_, v_stop_boxed_2912_, v_b_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec_ref(v_as_2902_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(lean_object* v_decls_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v___y_2921_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v___x_2924_ = lean_unsigned_to_nat(0u);
v___x_2925_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0));
v___x_2926_ = lean_array_get_size(v_decls_2914_);
v___x_2927_ = lean_nat_dec_lt(v___x_2924_, v___x_2926_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; 
v___x_2928_ = l_Lean_Compiler_LCNF_addBoxedVersions(v___x_2925_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
return v___x_2928_;
}
else
{
uint8_t v___x_2929_; 
v___x_2929_ = lean_nat_dec_le(v___x_2926_, v___x_2926_);
if (v___x_2929_ == 0)
{
if (v___x_2927_ == 0)
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_Compiler_LCNF_addBoxedVersions(v___x_2925_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
return v___x_2930_;
}
else
{
size_t v___x_2931_; size_t v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = ((size_t)0ULL);
v___x_2932_ = lean_usize_of_nat(v___x_2926_);
v___x_2933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_decls_2914_, v___x_2931_, v___x_2932_, v___x_2925_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
v___y_2921_ = v___x_2933_;
goto v___jp_2920_;
}
}
else
{
size_t v___x_2934_; size_t v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = ((size_t)0ULL);
v___x_2935_ = lean_usize_of_nat(v___x_2926_);
v___x_2936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_decls_2914_, v___x_2934_, v___x_2935_, v___x_2925_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
v___y_2921_ = v___x_2936_;
goto v___jp_2920_;
}
}
v___jp_2920_:
{
if (lean_obj_tag(v___y_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2923_; 
v_a_2922_ = lean_ctor_get(v___y_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref_known(v___y_2921_, 1);
v___x_2923_ = l_Lean_Compiler_LCNF_addBoxedVersions(v_a_2922_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
return v___x_2923_;
}
else
{
return v___y_2921_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run___boxed(lean_object* v_decls_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(v_decls_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec_ref(v_decls_2937_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3025_; uint8_t v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3025_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_));
v___x_3026_ = 1;
v___x_3027_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_));
v___x_3028_ = l_Lean_registerTraceClass(v___x_3025_, v___x_3026_, v___x_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2____boxed(lean_object* v_a_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_();
return v_res_3030_;
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
