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
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isVoid(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_CtorInfo_isScalar(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updatePapImp___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* v___x_5_; lean_object* v_type_6_; uint8_t v_borrow_7_; uint8_t v___x_8_; uint8_t v___x_9_; 
v___x_5_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v_type_6_ = lean_ctor_get(v___x_5_, 2);
v_borrow_7_ = lean_ctor_get_uint8(v___x_5_, sizeof(void*)*3);
v___x_8_ = 1;
v___x_9_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_6_);
if (v___x_9_ == 0)
{
if (v_borrow_7_ == 0)
{
uint8_t v___x_10_; 
v___x_10_ = l_Lean_Expr_isVoid(v_type_6_);
if (v___x_10_ == 0)
{
size_t v___x_11_; size_t v___x_12_; 
v___x_11_ = ((size_t)1ULL);
v___x_12_ = lean_usize_add(v_i_2_, v___x_11_);
v_i_2_ = v___x_12_;
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
else
{
return v___x_8_;
}
}
else
{
uint8_t v___x_14_; 
v___x_14_ = 0;
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0___boxed(lean_object* v_as_15_, lean_object* v_i_16_, lean_object* v_stop_17_){
_start:
{
size_t v_i_boxed_18_; size_t v_stop_boxed_19_; uint8_t v_res_20_; lean_object* v_r_21_; 
v_i_boxed_18_ = lean_unbox_usize(v_i_16_);
lean_dec(v_i_16_);
v_stop_boxed_19_ = lean_unbox_usize(v_stop_17_);
lean_dec(v_stop_17_);
v_res_20_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(v_as_15_, v_i_boxed_18_, v_stop_boxed_19_);
lean_dec_ref(v_as_15_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(lean_object* v_sig_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_name_25_; lean_object* v_type_26_; lean_object* v_params_27_; lean_object* v___x_28_; lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_name_25_ = lean_ctor_get(v_sig_22_, 0);
lean_inc(v_name_25_);
v_type_26_ = lean_ctor_get(v_sig_22_, 2);
lean_inc_ref(v_type_26_);
v_params_27_ = lean_ctor_get(v_sig_22_, 3);
lean_inc_ref(v_params_27_);
lean_dec_ref(v_sig_22_);
v___x_28_ = lean_st_ref_get(v_a_23_);
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_array_get_size(v_params_27_);
v___x_37_ = lean_nat_dec_lt(v___x_35_, v___x_36_);
if (v___x_37_ == 0)
{
lean_dec(v___x_28_);
lean_dec_ref(v_type_26_);
lean_dec(v_name_25_);
goto v___jp_29_;
}
else
{
uint8_t v___x_38_; 
v___x_38_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_26_);
lean_dec_ref(v_type_26_);
if (v___x_38_ == 0)
{
lean_object* v_env_39_; 
v_env_39_ = lean_ctor_get(v___x_28_, 0);
lean_inc_ref(v_env_39_);
lean_dec(v___x_28_);
if (v___x_37_ == 0)
{
goto v___jp_40_;
}
else
{
size_t v___x_44_; size_t v___x_45_; uint8_t v___x_46_; 
v___x_44_ = ((size_t)0ULL);
v___x_45_ = lean_usize_of_nat(v___x_36_);
v___x_46_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(v_params_27_, v___x_44_, v___x_45_);
if (v___x_46_ == 0)
{
goto v___jp_40_;
}
else
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec_ref(v_env_39_);
lean_dec_ref(v_params_27_);
lean_dec(v_name_25_);
v___x_47_ = lean_box(v___x_46_);
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
v___jp_40_:
{
uint8_t v___x_41_; 
v___x_41_ = l_Lean_isExtern(v_env_39_, v_name_25_);
if (v___x_41_ == 0)
{
goto v___jp_29_;
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; 
lean_dec_ref(v_params_27_);
v___x_42_ = lean_box(v___x_41_);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v___x_28_);
lean_dec_ref(v_params_27_);
lean_dec(v_name_25_);
v___x_49_ = lean_box(v___x_38_);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
v___jp_29_:
{
lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_30_ = l_Lean_closureMaxArgs;
v___x_31_ = lean_array_get_size(v_params_27_);
lean_dec_ref(v_params_27_);
v___x_32_ = lean_nat_dec_lt(v___x_30_, v___x_31_);
v___x_33_ = lean_box(v___x_32_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg___boxed(lean_object* v_sig_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_sig_51_, v_a_52_);
lean_dec(v_a_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion(lean_object* v_sig_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_sig_55_, v_a_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___boxed(lean_object* v_sig_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion(v_sig_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(size_t v_sz_69_, size_t v_i_70_, lean_object* v_bs_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
uint8_t v___x_77_; 
v___x_77_ = lean_usize_dec_lt(v_i_70_, v_sz_69_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; 
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v_bs_71_);
return v___x_78_;
}
else
{
lean_object* v_v_79_; lean_object* v_binderName_80_; lean_object* v_type_81_; lean_object* v___x_82_; lean_object* v_bs_x27_83_; uint8_t v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; 
v_v_79_ = lean_array_uget_borrowed(v_bs_71_, v_i_70_);
v_binderName_80_ = lean_ctor_get(v_v_79_, 1);
lean_inc(v_binderName_80_);
v_type_81_ = lean_ctor_get(v_v_79_, 2);
lean_inc_ref(v_type_81_);
v___x_82_ = lean_unsigned_to_nat(0u);
v_bs_x27_83_ = lean_array_uset(v_bs_71_, v_i_70_, v___x_82_);
v___x_84_ = 1;
v___x_85_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_81_);
lean_dec_ref(v_type_81_);
v___x_86_ = 0;
v___x_87_ = l_Lean_Compiler_LCNF_mkParam(v___x_84_, v_binderName_80_, v___x_85_, v___x_86_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; size_t v___x_89_; size_t v___x_90_; lean_object* v___x_91_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_88_);
lean_dec_ref_known(v___x_87_, 1);
v___x_89_ = ((size_t)1ULL);
v___x_90_ = lean_usize_add(v_i_70_, v___x_89_);
v___x_91_ = lean_array_uset(v_bs_x27_83_, v_i_70_, v_a_88_);
v_i_70_ = v___x_90_;
v_bs_71_ = v___x_91_;
goto _start;
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
lean_dec_ref(v_bs_x27_83_);
v_a_93_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_87_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_87_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0___boxed(lean_object* v_sz_101_, lean_object* v_i_102_, lean_object* v_bs_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
size_t v_sz_boxed_109_; size_t v_i_boxed_110_; lean_object* v_res_111_; 
v_sz_boxed_109_ = lean_unbox_usize(v_sz_101_);
lean_dec(v_sz_101_);
v_i_boxed_110_ = lean_unbox_usize(v_i_102_);
lean_dec(v_i_102_);
v_res_111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(v_sz_boxed_109_, v_i_boxed_110_, v_bs_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(lean_object* v_as_113_, size_t v_sz_114_, size_t v_i_115_, lean_object* v_b_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_a_123_; uint8_t v___x_127_; 
v___x_127_ = lean_usize_dec_lt(v_i_115_, v_sz_114_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v_b_116_);
return v___x_128_;
}
else
{
lean_object* v_snd_129_; lean_object* v_snd_130_; lean_object* v_fst_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_204_; 
v_snd_129_ = lean_ctor_get(v_b_116_, 1);
lean_inc(v_snd_129_);
v_snd_130_ = lean_ctor_get(v_snd_129_, 1);
lean_inc(v_snd_130_);
v_fst_131_ = lean_ctor_get(v_b_116_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v_b_116_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v_b_116_, 1);
lean_dec(v_unused_205_);
v___x_133_ = v_b_116_;
v_isShared_134_ = v_isSharedCheck_204_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_fst_131_);
lean_dec(v_b_116_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_204_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_fst_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_202_; 
v_fst_135_ = lean_ctor_get(v_snd_129_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v_snd_129_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v_snd_129_, 1);
lean_dec(v_unused_203_);
v___x_137_ = v_snd_129_;
v_isShared_138_ = v_isSharedCheck_202_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_fst_135_);
lean_dec(v_snd_129_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_202_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v_array_139_; lean_object* v_start_140_; lean_object* v_stop_141_; uint8_t v___x_142_; 
v_array_139_ = lean_ctor_get(v_snd_130_, 0);
v_start_140_ = lean_ctor_get(v_snd_130_, 1);
v_stop_141_ = lean_ctor_get(v_snd_130_, 2);
v___x_142_ = lean_nat_dec_lt(v_start_140_, v_stop_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_144_; 
if (v_isShared_138_ == 0)
{
v___x_144_ = v___x_137_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_fst_135_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_snd_130_);
v___x_144_ = v_reuseFailAlloc_149_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_146_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_144_);
v___x_146_ = v___x_133_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_fst_131_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_144_);
v___x_146_ = v_reuseFailAlloc_148_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
}
else
{
lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_198_; 
lean_inc(v_stop_141_);
lean_inc(v_start_140_);
lean_inc_ref(v_array_139_);
v_isSharedCheck_198_ = !lean_is_exclusive(v_snd_130_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; lean_object* v_unused_200_; lean_object* v_unused_201_; 
v_unused_199_ = lean_ctor_get(v_snd_130_, 2);
lean_dec(v_unused_199_);
v_unused_200_ = lean_ctor_get(v_snd_130_, 1);
lean_dec(v_unused_200_);
v_unused_201_ = lean_ctor_get(v_snd_130_, 0);
lean_dec(v_unused_201_);
v___x_151_ = v_snd_130_;
v_isShared_152_ = v_isSharedCheck_198_;
goto v_resetjp_150_;
}
else
{
lean_dec(v_snd_130_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_198_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v_a_153_; lean_object* v_binderName_154_; lean_object* v_type_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v_a_153_ = lean_array_uget_borrowed(v_as_113_, v_i_115_);
v_binderName_154_ = lean_ctor_get(v_a_153_, 1);
v_type_155_ = lean_ctor_get(v_a_153_, 2);
v___x_156_ = lean_array_fget(v_array_139_, v_start_140_);
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_add(v_start_140_, v___x_157_);
lean_dec(v_start_140_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v___x_158_);
v___x_160_ = v___x_151_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_array_139_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_stop_141_);
v___x_160_ = v_reuseFailAlloc_197_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
uint8_t v___x_161_; 
v___x_161_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_155_);
if (v___x_161_ == 0)
{
lean_object* v_fvarId_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v_fvarId_162_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_fvarId_162_);
lean_dec(v___x_156_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v_fvarId_162_);
v___x_164_ = lean_array_push(v_fst_135_, v___x_163_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v___x_160_);
lean_ctor_set(v___x_137_, 0, v___x_164_);
v___x_166_ = v___x_137_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_160_);
v___x_166_ = v_reuseFailAlloc_170_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_166_);
v___x_168_ = v___x_133_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_fst_131_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
v_a_123_ = v___x_168_;
goto v___jp_122_;
}
}
}
else
{
lean_object* v_fvarId_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_fvarId_171_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_fvarId_171_);
lean_dec(v___x_156_);
v___x_172_ = 1;
v___x_173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0));
lean_inc(v_binderName_154_);
v___x_174_ = l_Lean_Name_str___override(v_binderName_154_, v___x_173_);
v___x_175_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_175_, 0, v_fvarId_171_);
lean_inc_ref(v_type_155_);
v___x_176_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_172_, v___x_174_, v_type_155_, v___x_175_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v_fvarId_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_176_, 1);
v_fvarId_178_ = lean_ctor_get(v_a_177_, 0);
lean_inc(v_fvarId_178_);
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v_a_177_);
v___x_180_ = lean_array_push(v_fst_131_, v___x_179_);
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_fvarId_178_);
v___x_182_ = lean_array_push(v_fst_135_, v___x_181_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v___x_160_);
lean_ctor_set(v___x_137_, 0, v___x_182_);
v___x_184_ = v___x_137_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_160_);
v___x_184_ = v_reuseFailAlloc_188_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_186_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_184_);
lean_ctor_set(v___x_133_, 0, v___x_180_);
v___x_186_ = v___x_133_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
v_a_123_ = v___x_186_;
goto v___jp_122_;
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
lean_dec_ref(v___x_160_);
lean_del_object(v___x_137_);
lean_dec(v_fst_135_);
lean_del_object(v___x_133_);
lean_dec(v_fst_131_);
v_a_189_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_176_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_176_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
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
v___jp_122_:
{
size_t v___x_124_; size_t v___x_125_; 
v___x_124_ = ((size_t)1ULL);
v___x_125_ = lean_usize_add(v_i_115_, v___x_124_);
v_i_115_ = v___x_125_;
v_b_116_ = v_a_123_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___boxed(lean_object* v_as_206_, lean_object* v_sz_207_, lean_object* v_i_208_, lean_object* v_b_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
size_t v_sz_boxed_215_; size_t v_i_boxed_216_; lean_object* v_res_217_; 
v_sz_boxed_215_ = lean_unbox_usize(v_sz_207_);
lean_dec(v_sz_207_);
v_i_boxed_216_ = lean_unbox_usize(v_i_208_);
lean_dec(v_i_208_);
v_res_217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(v_as_206_, v_sz_boxed_215_, v_i_boxed_216_, v_b_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec_ref(v_as_206_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(lean_object* v_sig_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_name_232_; lean_object* v_type_233_; lean_object* v_params_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_353_; 
v_name_232_ = lean_ctor_get(v_sig_226_, 0);
v_type_233_ = lean_ctor_get(v_sig_226_, 2);
v_params_234_ = lean_ctor_get(v_sig_226_, 3);
v_isSharedCheck_353_ = !lean_is_exclusive(v_sig_226_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; 
v_unused_354_ = lean_ctor_get(v_sig_226_, 1);
lean_dec(v_unused_354_);
v___x_236_ = v_sig_226_;
v_isShared_237_ = v_isSharedCheck_353_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_params_234_);
lean_inc(v_type_233_);
lean_inc(v_name_232_);
lean_dec(v_sig_226_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_353_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
size_t v_sz_238_; size_t v___x_239_; lean_object* v___x_240_; 
v_sz_238_ = lean_array_size(v_params_234_);
v___x_239_ = ((size_t)0ULL);
lean_inc_ref(v_params_234_);
v___x_240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(v_sz_238_, v___x_239_, v_params_234_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v_value_243_; lean_object* v___y_244_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc_n(v_a_241_, 2);
lean_dec_ref_known(v___x_240_, 1);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0));
v___x_275_ = lean_array_get_size(v_params_234_);
v___x_276_ = lean_mk_empty_array_with_capacity(v___x_275_);
v___x_277_ = lean_array_get_size(v_a_241_);
v___x_278_ = l_Array_toSubarray___redArg(v_a_241_, v___x_273_, v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_276_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_274_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(v_params_234_, v_sz_238_, v___x_239_, v___x_280_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
lean_dec_ref(v_params_234_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v_snd_283_; lean_object* v_fst_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_336_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_a_282_);
lean_dec_ref_known(v___x_281_, 1);
v_snd_283_ = lean_ctor_get(v_a_282_, 1);
v_fst_284_ = lean_ctor_get(v_a_282_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_a_282_);
if (v_isSharedCheck_336_ == 0)
{
v___x_286_ = v_a_282_;
v_isShared_287_ = v_isSharedCheck_336_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_snd_283_);
lean_inc(v_fst_284_);
lean_dec(v_a_282_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_336_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v_fst_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_334_; 
v_fst_288_ = lean_ctor_get(v_snd_283_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_snd_283_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v_snd_283_, 1);
lean_dec(v_unused_335_);
v___x_290_ = v_snd_283_;
v_isShared_291_ = v_isSharedCheck_334_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_fst_288_);
lean_dec(v_snd_283_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_334_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_292_ = 1;
v___x_293_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2));
lean_inc(v_name_232_);
if (v_isShared_291_ == 0)
{
lean_ctor_set_tag(v___x_290_, 9);
lean_ctor_set(v___x_290_, 1, v_fst_288_);
lean_ctor_set(v___x_290_, 0, v_name_232_);
v___x_295_ = v___x_290_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_name_232_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_fst_288_);
v___x_295_ = v_reuseFailAlloc_333_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; 
lean_inc_ref(v_type_233_);
v___x_296_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_292_, v___x_293_, v_type_233_, v___x_295_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc_n(v_a_297_, 2);
lean_dec_ref_known(v___x_296_, 1);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v_a_297_);
v___x_299_ = lean_array_push(v_fst_284_, v___x_298_);
v___x_300_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_233_);
if (v___x_300_ == 0)
{
lean_object* v_fvarId_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_del_object(v___x_286_);
v_fvarId_301_ = lean_ctor_get(v_a_297_, 0);
lean_inc(v_fvarId_301_);
lean_dec(v_a_297_);
v___x_302_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_302_, 0, v_fvarId_301_);
v___x_303_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___x_299_, v___x_302_);
lean_dec_ref(v___x_299_);
v_value_243_ = v___x_303_;
v___y_244_ = v_a_230_;
goto v___jp_242_;
}
else
{
lean_object* v_fvarId_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v_fvarId_304_ = lean_ctor_get(v_a_297_, 0);
lean_inc(v_fvarId_304_);
lean_dec(v_a_297_);
v___x_305_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4));
v___x_306_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_233_);
lean_inc_ref(v_type_233_);
if (v_isShared_287_ == 0)
{
lean_ctor_set_tag(v___x_286_, 13);
lean_ctor_set(v___x_286_, 1, v_fvarId_304_);
lean_ctor_set(v___x_286_, 0, v_type_233_);
v___x_308_ = v___x_286_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_type_233_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_fvarId_304_);
v___x_308_ = v_reuseFailAlloc_324_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_292_, v___x_305_, v___x_306_, v___x_308_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v_fvarId_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v_fvarId_311_ = lean_ctor_get(v_a_310_, 0);
lean_inc(v_fvarId_311_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v_a_310_);
v___x_313_ = lean_array_push(v___x_299_, v___x_312_);
v___x_314_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_314_, 0, v_fvarId_311_);
v___x_315_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___x_313_, v___x_314_);
lean_dec_ref(v___x_313_);
v_value_243_ = v___x_315_;
v___y_244_ = v_a_230_;
goto v___jp_242_;
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v___x_299_);
lean_dec(v_a_241_);
lean_del_object(v___x_236_);
lean_dec_ref(v_type_233_);
lean_dec(v_name_232_);
v_a_316_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_309_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_309_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_del_object(v___x_286_);
lean_dec(v_fst_284_);
lean_dec(v_a_241_);
lean_del_object(v___x_236_);
lean_dec_ref(v_type_233_);
lean_dec(v_name_232_);
v_a_325_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_296_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_296_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec(v_a_241_);
lean_del_object(v___x_236_);
lean_dec_ref(v_type_233_);
lean_dec(v_name_232_);
v_a_337_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_281_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_281_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
v___jp_242_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; lean_object* v___x_250_; 
v___x_245_ = l_Lean_Compiler_LCNF_mkBoxedName(v_name_232_);
v___x_246_ = lean_box(0);
v___x_247_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_233_);
lean_dec_ref(v_type_233_);
v___x_248_ = 1;
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 3, v_a_241_);
lean_ctor_set(v___x_236_, 2, v___x_247_);
lean_ctor_set(v___x_236_, 1, v___x_246_);
lean_ctor_set(v___x_236_, 0, v___x_245_);
v___x_250_ = v___x_236_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_a_241_);
v___x_250_ = v_reuseFailAlloc_272_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*4, v___x_248_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v_value_243_);
v___x_252_ = 0;
v___x_253_ = lean_box(0);
v___x_254_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_254_, 0, v___x_250_);
lean_ctor_set(v___x_254_, 1, v___x_251_);
lean_ctor_set(v___x_254_, 2, v___x_253_);
lean_ctor_set_uint8(v___x_254_, sizeof(void*)*3, v___x_252_);
lean_inc_ref(v___x_254_);
v___x_255_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v___x_254_, v___y_244_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v___x_255_, 0);
lean_dec(v_unused_263_);
v___x_257_ = v___x_255_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_dec(v___x_255_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_254_);
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_254_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec_ref_known(v___x_254_, 3);
v_a_264_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_255_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_255_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_del_object(v___x_236_);
lean_dec_ref(v_params_234_);
lean_dec_ref(v_type_233_);
lean_dec(v_name_232_);
v_a_345_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_240_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_240_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___boxed(lean_object* v_sig_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(v_sig_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(lean_object* v_as_362_, size_t v_i_363_, size_t v_stop_364_, lean_object* v_b_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_a_372_; uint8_t v___x_376_; 
v___x_376_ = lean_usize_dec_eq(v_i_363_, v_stop_364_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v_toSignature_378_; lean_object* v___x_379_; 
v___x_377_ = lean_array_uget_borrowed(v_as_362_, v_i_363_);
v_toSignature_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc_ref(v_toSignature_378_);
v___x_379_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_toSignature_378_, v___y_369_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; uint8_t v___x_381_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_379_, 1);
v___x_381_ = lean_unbox(v_a_380_);
lean_dec(v_a_380_);
if (v___x_381_ == 0)
{
v_a_372_ = v_b_365_;
goto v___jp_371_;
}
else
{
lean_object* v___x_382_; 
lean_inc_ref(v_toSignature_378_);
v___x_382_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(v_toSignature_378_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
v___x_384_ = lean_array_push(v_b_365_, v_a_383_);
v_a_372_ = v___x_384_;
goto v___jp_371_;
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec_ref(v_b_365_);
v_a_385_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_382_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_382_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
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
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref(v_b_365_);
v_a_393_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_379_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_379_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v___x_401_; 
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v_b_365_);
return v___x_401_;
}
v___jp_371_:
{
size_t v___x_373_; size_t v___x_374_; 
v___x_373_ = ((size_t)1ULL);
v___x_374_ = lean_usize_add(v_i_363_, v___x_373_);
v_i_363_ = v___x_374_;
v_b_365_ = v_a_372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0___boxed(lean_object* v_as_402_, lean_object* v_i_403_, lean_object* v_stop_404_, lean_object* v_b_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
size_t v_i_boxed_411_; size_t v_stop_boxed_412_; lean_object* v_res_413_; 
v_i_boxed_411_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_stop_boxed_412_ = lean_unbox_usize(v_stop_404_);
lean_dec(v_stop_404_);
v_res_413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_402_, v_i_boxed_411_, v_stop_boxed_412_, v_b_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec_ref(v_as_402_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(lean_object* v_as_416_, lean_object* v_start_417_, lean_object* v_stop_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0));
v___x_425_ = lean_nat_dec_lt(v_start_417_, v_stop_418_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = lean_array_get_size(v_as_416_);
v___x_428_ = lean_nat_dec_le(v_stop_418_, v___x_427_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; 
v___x_429_ = lean_nat_dec_lt(v_start_417_, v___x_427_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_424_);
return v___x_430_;
}
else
{
size_t v___x_431_; size_t v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_usize_of_nat(v_start_417_);
v___x_432_ = lean_usize_of_nat(v___x_427_);
v___x_433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_416_, v___x_431_, v___x_432_, v___x_424_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
return v___x_433_;
}
}
else
{
size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_usize_of_nat(v_start_417_);
v___x_435_ = lean_usize_of_nat(v_stop_418_);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_416_, v___x_434_, v___x_435_, v___x_424_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___boxed(lean_object* v_as_437_, lean_object* v_start_438_, lean_object* v_stop_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(v_as_437_, v_start_438_, v_stop_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v_stop_439_);
lean_dec(v_start_438_);
lean_dec_ref(v_as_437_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addBoxedVersions(lean_object* v_decls_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_array_get_size(v_decls_446_);
v___x_454_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(v_decls_446_, v___x_452_, v___x_453_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_463_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_463_ == 0)
{
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = l_Array_append___redArg(v_decls_446_, v_a_455_);
lean_dec(v_a_455_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_459_);
v___x_461_ = v___x_457_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
else
{
lean_dec_ref(v_decls_446_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addBoxedVersions___boxed(lean_object* v_decls_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Compiler_LCNF_addBoxedVersions(v_decls_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(lean_object* v_a_471_){
_start:
{
lean_object* v_currDeclResultType_473_; lean_object* v___x_474_; 
v_currDeclResultType_473_ = lean_ctor_get(v_a_471_, 1);
lean_inc_ref(v_currDeclResultType_473_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v_currDeclResultType_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg___boxed(lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(v_a_475_);
lean_dec_ref(v_a_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_currDeclResultType_485_; lean_object* v___x_486_; 
v_currDeclResultType_485_ = lean_ctor_get(v_a_478_, 1);
lean_inc_ref(v_currDeclResultType_485_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v_currDeclResultType_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___boxed(lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
return v_res_494_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(lean_object* v_t_u2081_495_, lean_object* v_t_u2082_496_){
_start:
{
uint8_t v___y_498_; uint8_t v___x_501_; uint8_t v___x_502_; 
v___x_501_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2081_495_);
v___x_502_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2082_496_);
if (v___x_502_ == 0)
{
if (v___x_501_ == 0)
{
uint8_t v___x_503_; 
v___x_503_ = 1;
v___y_498_ = v___x_503_;
goto v___jp_497_;
}
else
{
return v___x_502_;
}
}
else
{
if (v___x_501_ == 0)
{
return v___x_501_;
}
else
{
v___y_498_ = v___x_501_;
goto v___jp_497_;
}
}
v___jp_497_:
{
uint8_t v___x_499_; 
v___x_499_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2081_495_);
if (v___x_499_ == 0)
{
return v___y_498_;
}
else
{
uint8_t v___x_500_; 
v___x_500_ = lean_expr_eqv(v_t_u2081_495_, v_t_u2082_496_);
return v___x_500_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing___boxed(lean_object* v_t_u2081_504_, lean_object* v_t_u2082_505_){
_start:
{
uint8_t v_res_506_; lean_object* v_r_507_; 
v_res_506_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_t_u2081_504_, v_t_u2082_505_);
lean_dec_ref(v_t_u2082_505_);
lean_dec_ref(v_t_u2081_504_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(lean_object* v_x_510_, lean_object* v_xType_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___y_515_; 
if (lean_obj_tag(v_xType_511_) == 4)
{
lean_object* v_declName_554_; 
v_declName_554_ = lean_ctor_get(v_xType_511_, 0);
if (lean_obj_tag(v_declName_554_) == 1)
{
lean_object* v_pre_555_; 
v_pre_555_ = lean_ctor_get(v_declName_554_, 0);
if (lean_obj_tag(v_pre_555_) == 0)
{
lean_object* v_us_556_; lean_object* v_str_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v_us_556_ = lean_ctor_get(v_xType_511_, 1);
v_str_557_ = lean_ctor_get(v_declName_554_, 1);
v___x_558_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0));
v___x_559_ = lean_string_dec_eq(v_str_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1));
v___x_561_ = lean_string_dec_eq(v_str_557_, v___x_560_);
if (v___x_561_ == 0)
{
v___y_515_ = v_a_512_;
goto v___jp_514_;
}
else
{
if (lean_obj_tag(v_us_556_) == 0)
{
goto v___jp_551_;
}
else
{
v___y_515_ = v_a_512_;
goto v___jp_514_;
}
}
}
else
{
if (lean_obj_tag(v_us_556_) == 0)
{
goto v___jp_551_;
}
else
{
v___y_515_ = v_a_512_;
goto v___jp_514_;
}
}
}
else
{
v___y_515_ = v_a_512_;
goto v___jp_514_;
}
}
else
{
v___y_515_ = v_a_512_;
goto v___jp_514_;
}
}
else
{
v___y_515_ = v_a_512_;
goto v___jp_514_;
}
v___jp_514_:
{
uint8_t v___x_516_; lean_object* v___x_517_; 
v___x_516_ = 1;
v___x_517_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_516_, v_x_510_, v___y_515_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
if (lean_obj_tag(v_a_518_) == 1)
{
lean_object* v_val_519_; 
v_val_519_ = lean_ctor_get(v_a_518_, 0);
switch(lean_obj_tag(v_val_519_))
{
case 0:
{
return v___x_517_;
}
case 9:
{
lean_object* v_args_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v_args_520_ = lean_ctor_get(v_val_519_, 1);
v___x_521_ = lean_array_get_size(v_args_520_);
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_nat_dec_eq(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_531_; 
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v___x_517_, 0);
lean_dec(v_unused_532_);
v___x_525_ = v___x_517_;
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
else
{
lean_dec(v___x_517_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_box(0);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
else
{
return v___x_517_;
}
}
default: 
{
lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_540_; 
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; 
v_unused_541_ = lean_ctor_get(v___x_517_, 0);
lean_dec(v_unused_541_);
v___x_534_ = v___x_517_;
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
else
{
lean_dec(v___x_517_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_box(0);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_536_);
v___x_538_ = v___x_534_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
else
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_549_; 
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v___x_517_, 0);
lean_dec(v_unused_550_);
v___x_543_ = v___x_517_;
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
else
{
lean_dec(v___x_517_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_box(0);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
else
{
return v___x_517_;
}
}
v___jp_551_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_box(0);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___boxed(lean_object* v_x_562_, lean_object* v_xType_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_x_562_, v_xType_563_, v_a_564_);
lean_dec(v_a_564_);
lean_dec_ref(v_xType_563_);
lean_dec(v_x_562_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(lean_object* v_x_567_, lean_object* v_xType_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_x_567_, v_xType_568_, v_a_572_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___boxed(lean_object* v_x_577_, lean_object* v_xType_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(v_x_577_, v_xType_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec_ref(v_xType_578_);
lean_dec(v_x_577_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(lean_object* v_fvarId_592_, lean_object* v_fvarIdType_593_, lean_object* v_expectedType_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
uint8_t v___x_602_; 
v___x_602_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_expectedType_594_);
if (v___x_602_ == 0)
{
uint8_t v___x_603_; lean_object* v___x_604_; 
v___x_603_ = 1;
v___x_604_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_fvarId_592_, v_fvarIdType_593_, v_a_598_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_730_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_730_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_730_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_730_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
if (lean_obj_tag(v_a_605_) == 0)
{
lean_object* v___x_609_; lean_object* v___x_611_; 
lean_dec_ref(v_expectedType_594_);
v___x_609_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_609_, 0, v_fvarIdType_593_);
lean_ctor_set(v___x_609_, 1, v_fvarId_592_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
else
{
lean_object* v_val_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_729_; 
lean_del_object(v___x_607_);
lean_dec(v_fvarId_592_);
v_val_613_ = lean_ctor_get(v_a_605_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v_a_605_);
if (v_isSharedCheck_729_ == 0)
{
v___x_615_ = v_a_605_;
v_isShared_616_ = v_isSharedCheck_729_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_val_613_);
lean_dec(v_a_605_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_729_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = 1;
v___x_618_ = lean_box(0);
lean_inc_ref(v_fvarIdType_593_);
v___x_619_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_617_, v___x_618_, v_fvarIdType_593_, v_val_613_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v_fvarId_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_619_, 1);
v_fvarId_621_ = lean_ctor_get(v_a_620_, 0);
lean_inc(v_fvarId_621_);
v___x_622_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_622_, 0, v_fvarIdType_593_);
lean_ctor_set(v___x_622_, 1, v_fvarId_621_);
lean_inc_ref(v_expectedType_594_);
v___x_623_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_617_, v___x_618_, v_expectedType_594_, v___x_622_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v_fvarId_625_; lean_object* v___x_627_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v_fvarId_625_ = lean_ctor_get(v_a_624_, 0);
lean_inc(v_fvarId_625_);
if (v_isShared_616_ == 0)
{
lean_ctor_set_tag(v___x_615_, 5);
lean_ctor_set(v___x_615_, 0, v_fvarId_625_);
v___x_627_ = v___x_615_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_fvarId_625_);
v___x_627_ = v_reuseFailAlloc_712_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_currDecl_631_; lean_object* v_nextAuxIdx_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_710_; 
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v_a_624_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_a_620_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = lean_st_ref_get(v_a_596_);
v_currDecl_631_ = lean_ctor_get(v_a_595_, 0);
v_nextAuxIdx_632_ = lean_ctor_get(v___x_630_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v___x_630_, 0);
lean_dec(v_unused_711_);
v___x_634_ = v___x_630_;
v_isShared_635_ = v_isSharedCheck_710_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_nextAuxIdx_632_);
lean_dec(v___x_630_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_710_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_636_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__1));
v___x_637_ = lean_name_append_index_after(v___x_636_, v_nextAuxIdx_632_);
lean_inc(v_currDecl_631_);
v___x_638_ = l_Lean_Name_append(v_currDecl_631_, v___x_637_);
v___x_639_ = lean_box(0);
v___x_640_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__2));
lean_inc(v___x_638_);
v___x_641_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_641_, 0, v___x_638_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
lean_ctor_set(v___x_641_, 2, v_expectedType_594_);
lean_ctor_set(v___x_641_, 3, v___x_640_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*4, v___x_603_);
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_629_);
v___x_643_ = lean_box(0);
v___x_644_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_644_, 0, v___x_641_);
lean_ctor_set(v___x_644_, 1, v___x_642_);
lean_ctor_set(v___x_644_, 2, v___x_643_);
lean_ctor_set_uint8(v___x_644_, sizeof(void*)*3, v___x_602_);
lean_inc_ref(v___x_644_);
v___x_645_ = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(v___x_617_, v___x_644_, v_a_599_, v_a_600_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
if (lean_obj_tag(v_a_646_) == 0)
{
lean_object* v___x_647_; lean_object* v_auxDecls_648_; lean_object* v_nextAuxIdx_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_680_; 
v___x_647_ = lean_st_ref_take(v_a_596_);
v_auxDecls_648_ = lean_ctor_get(v___x_647_, 0);
v_nextAuxIdx_649_ = lean_ctor_get(v___x_647_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_680_ == 0)
{
v___x_651_ = v___x_647_;
v_isShared_652_ = v_isSharedCheck_680_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_nextAuxIdx_649_);
lean_inc(v_auxDecls_648_);
lean_dec(v___x_647_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_680_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
lean_inc_ref(v___x_644_);
v___x_653_ = lean_array_push(v_auxDecls_648_, v___x_644_);
v___x_654_ = lean_unsigned_to_nat(1u);
v___x_655_ = lean_nat_add(v_nextAuxIdx_649_, v___x_654_);
lean_dec(v_nextAuxIdx_649_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v___x_655_);
lean_ctor_set(v___x_651_, 0, v___x_653_);
v___x_657_ = v___x_651_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_655_);
v___x_657_ = v_reuseFailAlloc_679_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_st_ref_put(v_a_596_, v___x_657_);
v___x_659_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v___x_644_, v_a_600_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_669_; 
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v___x_659_, 0);
lean_dec(v_unused_670_);
v___x_661_ = v___x_659_;
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
else
{
lean_dec(v___x_659_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 9);
lean_ctor_set(v___x_634_, 1, v___x_640_);
lean_ctor_set(v___x_634_, 0, v___x_638_);
v___x_664_ = v___x_634_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_640_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_664_);
v___x_666_ = v___x_661_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec(v___x_638_);
lean_del_object(v___x_634_);
v_a_671_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_659_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_659_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
else
{
lean_object* v_declName_681_; lean_object* v___x_682_; 
lean_dec(v___x_638_);
v_declName_681_ = lean_ctor_get(v_a_646_, 0);
lean_inc(v_declName_681_);
lean_dec_ref_known(v_a_646_, 1);
v___x_682_ = l_Lean_Compiler_LCNF_eraseDecl(v___x_617_, v___x_644_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_692_; 
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; 
v_unused_693_ = lean_ctor_get(v___x_682_, 0);
lean_dec(v_unused_693_);
v___x_684_ = v___x_682_;
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
else
{
lean_dec(v___x_682_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 9);
lean_ctor_set(v___x_634_, 1, v___x_640_);
lean_ctor_set(v___x_634_, 0, v_declName_681_);
v___x_687_ = v___x_634_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_declName_681_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_640_);
v___x_687_ = v_reuseFailAlloc_691_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_689_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_687_);
v___x_689_ = v___x_684_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec(v_declName_681_);
lean_del_object(v___x_634_);
v_a_694_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_682_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_682_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
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
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref_known(v___x_644_, 3);
lean_dec(v___x_638_);
lean_del_object(v___x_634_);
v_a_702_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_645_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_645_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v_a_620_);
lean_del_object(v___x_615_);
lean_dec_ref(v_expectedType_594_);
v_a_713_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_623_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_623_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_del_object(v___x_615_);
lean_dec_ref(v_expectedType_594_);
lean_dec_ref(v_fvarIdType_593_);
v_a_721_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_619_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_619_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v_expectedType_594_);
lean_dec_ref(v_fvarIdType_593_);
lean_dec(v_fvarId_592_);
v_a_731_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_604_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_604_);
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
else
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec_ref(v_expectedType_594_);
lean_dec_ref(v_fvarIdType_593_);
v___x_739_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_739_, 0, v_fvarId_592_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___boxed(lean_object* v_fvarId_741_, lean_object* v_fvarIdType_742_, lean_object* v_expectedType_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_741_, v_fvarIdType_742_, v_expectedType_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(lean_object* v_fvarId_752_, lean_object* v_expectedType_753_, lean_object* v_k_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v___x_762_; 
lean_inc(v_fvarId_752_);
v___x_762_ = l_Lean_Compiler_LCNF_getType(v_fvarId_752_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; uint8_t v___x_764_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v___x_764_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_763_, v_expectedType_753_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
lean_inc_ref(v_expectedType_753_);
v___x_765_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_752_, v_a_763_, v_expectedType_753_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = 1;
v___x_768_ = lean_box(0);
v___x_769_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_767_, v___x_768_, v_expectedType_753_, v_a_766_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v_fvarId_771_; lean_object* v___x_772_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_769_, 1);
v_fvarId_771_ = lean_ctor_get(v_a_770_, 0);
lean_inc(v_a_760_);
lean_inc_ref(v_a_759_);
lean_inc(v_a_758_);
lean_inc_ref(v_a_757_);
lean_inc(v_a_756_);
lean_inc_ref(v_a_755_);
lean_inc(v_fvarId_771_);
v___x_772_ = lean_apply_8(v_k_754_, v_fvarId_771_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, lean_box(0));
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_781_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_781_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_781_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_781_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_a_770_);
lean_ctor_set(v___x_777_, 1, v_a_773_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_777_);
v___x_779_ = v___x_775_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
else
{
lean_dec(v_a_770_);
return v___x_772_;
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec_ref(v_k_754_);
v_a_782_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_769_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_769_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v_k_754_);
lean_dec_ref(v_expectedType_753_);
v_a_790_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_765_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_765_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v___x_798_; 
lean_dec(v_a_763_);
lean_dec_ref(v_expectedType_753_);
lean_inc(v_a_760_);
lean_inc_ref(v_a_759_);
lean_inc(v_a_758_);
lean_inc_ref(v_a_757_);
lean_inc(v_a_756_);
lean_inc_ref(v_a_755_);
v___x_798_ = lean_apply_8(v_k_754_, v_fvarId_752_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, lean_box(0));
return v___x_798_;
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v_k_754_);
lean_dec_ref(v_expectedType_753_);
lean_dec(v_fvarId_752_);
v_a_799_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_762_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_762_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded___boxed(lean_object* v_fvarId_807_, lean_object* v_expectedType_808_, lean_object* v_k_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(v_fvarId_807_, v_expectedType_808_, v_k_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(lean_object* v_arg_818_, lean_object* v_k_819_, lean_object* v_x_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(v_arg_818_, v_x_820_);
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
lean_inc(v___y_822_);
lean_inc_ref(v___y_821_);
v___x_829_ = lean_apply_8(v_k_819_, v___x_828_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, lean_box(0));
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0___boxed(lean_object* v_arg_830_, lean_object* v_k_831_, lean_object* v_x_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_830_, v_k_831_, v_x_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(lean_object* v_arg_841_, lean_object* v_expectedType_842_, lean_object* v_k_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
if (lean_obj_tag(v_arg_841_) == 0)
{
lean_object* v___x_851_; 
lean_dec_ref(v_expectedType_842_);
lean_inc(v_a_849_);
lean_inc_ref(v_a_848_);
lean_inc(v_a_847_);
lean_inc_ref(v_a_846_);
lean_inc(v_a_845_);
lean_inc_ref(v_a_844_);
v___x_851_ = lean_apply_8(v_k_843_, v_arg_841_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, lean_box(0));
return v___x_851_;
}
else
{
lean_object* v_fvarId_852_; lean_object* v___x_853_; 
v_fvarId_852_ = lean_ctor_get(v_arg_841_, 0);
lean_inc(v_fvarId_852_);
v___x_853_ = l_Lean_Compiler_LCNF_getType(v_fvarId_852_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; uint8_t v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_854_, v_expectedType_842_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_inc_ref(v_expectedType_842_);
lean_inc(v_fvarId_852_);
v___x_856_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_852_, v_a_854_, v_expectedType_842_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
v___x_858_ = 1;
v___x_859_ = lean_box(0);
v___x_860_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_858_, v___x_859_, v_expectedType_842_, v_a_857_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v_fvarId_862_; lean_object* v___x_863_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v_fvarId_862_ = lean_ctor_get(v_a_861_, 0);
lean_inc(v_fvarId_862_);
v___x_863_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_841_, v_k_843_, v_fvarId_862_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_872_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_872_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v_a_861_);
lean_ctor_set(v___x_868_, 1, v_a_864_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_dec(v_a_861_);
return v___x_863_;
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref_known(v_arg_841_, 1);
lean_dec_ref(v_k_843_);
v_a_873_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_860_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_860_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref_known(v_arg_841_, 1);
lean_dec_ref(v_k_843_);
lean_dec_ref(v_expectedType_842_);
v_a_881_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_856_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_856_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v___x_889_; 
lean_inc(v_fvarId_852_);
lean_dec(v_a_854_);
lean_dec_ref(v_expectedType_842_);
v___x_889_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_841_, v_k_843_, v_fvarId_852_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
return v___x_889_;
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref_known(v_arg_841_, 1);
lean_dec_ref(v_k_843_);
lean_dec_ref(v_expectedType_842_);
v_a_890_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_853_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_853_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___boxed(lean_object* v_arg_898_, lean_object* v_expectedType_899_, lean_object* v_k_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(v_arg_898_, v_expectedType_899_, v_k_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(lean_object* v_upperBound_909_, lean_object* v_args_910_, lean_object* v_typeFromIdx_911_, lean_object* v_a_912_, lean_object* v_b_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_a_922_; uint8_t v___x_926_; 
v___x_926_ = lean_nat_dec_lt(v_a_912_, v_upperBound_909_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
lean_dec(v_a_912_);
lean_dec_ref(v_typeFromIdx_911_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_b_913_);
return v___x_927_;
}
else
{
lean_object* v_fst_928_; lean_object* v_snd_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_992_; 
v_fst_928_ = lean_ctor_get(v_b_913_, 0);
v_snd_929_ = lean_ctor_get(v_b_913_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_b_913_);
if (v_isSharedCheck_992_ == 0)
{
v___x_931_ = v_b_913_;
v_isShared_932_ = v_isSharedCheck_992_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_snd_929_);
lean_inc(v_fst_928_);
lean_dec(v_b_913_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_992_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; 
v___x_933_ = lean_array_fget(v_args_910_, v_a_912_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_934_ = lean_array_push(v_fst_928_, v___x_933_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_934_);
v___x_936_ = v___x_931_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_snd_929_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
v_a_922_ = v___x_936_;
goto v___jp_921_;
}
}
else
{
lean_object* v_fvarId_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_fvarId_938_ = lean_ctor_get(v___x_933_, 0);
lean_inc_ref(v_typeFromIdx_911_);
lean_inc(v_a_912_);
v___x_939_ = lean_apply_1(v_typeFromIdx_911_, v_a_912_);
lean_inc(v_fvarId_938_);
v___x_940_ = l_Lean_Compiler_LCNF_getType(v_fvarId_938_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; uint8_t v___x_942_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
v___x_942_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_941_, v___x_939_);
if (v___x_942_ == 0)
{
lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_978_; 
lean_inc(v_fvarId_938_);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; 
v_unused_979_ = lean_ctor_get(v___x_933_, 0);
lean_dec(v_unused_979_);
v___x_944_ = v___x_933_;
v_isShared_945_ = v_isSharedCheck_978_;
goto v_resetjp_943_;
}
else
{
lean_dec(v___x_933_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_978_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; 
lean_inc_ref(v___x_939_);
v___x_946_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_938_, v_a_941_, v___x_939_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
v___x_948_ = 1;
v___x_949_ = lean_box(0);
v___x_950_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_948_, v___x_949_, v___x_939_, v_a_947_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v_fvarId_952_; lean_object* v___x_954_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v_fvarId_952_ = lean_ctor_get(v_a_951_, 0);
lean_inc(v_fvarId_952_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v_fvarId_952_);
v___x_954_ = v___x_944_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_fvarId_952_);
v___x_954_ = v_reuseFailAlloc_961_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_955_ = lean_array_push(v_fst_928_, v___x_954_);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v_a_951_);
v___x_957_ = lean_array_push(v_snd_929_, v___x_956_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_957_);
lean_ctor_set(v___x_931_, 0, v___x_955_);
v___x_959_ = v___x_931_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
v_a_922_ = v___x_959_;
goto v___jp_921_;
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_del_object(v___x_944_);
lean_del_object(v___x_931_);
lean_dec(v_snd_929_);
lean_dec(v_fst_928_);
lean_dec(v_a_912_);
lean_dec_ref(v_typeFromIdx_911_);
v_a_962_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_950_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_950_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_del_object(v___x_944_);
lean_dec_ref(v___x_939_);
lean_del_object(v___x_931_);
lean_dec(v_snd_929_);
lean_dec(v_fst_928_);
lean_dec(v_a_912_);
lean_dec_ref(v_typeFromIdx_911_);
v_a_970_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_946_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_946_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
else
{
lean_object* v___x_980_; lean_object* v___x_982_; 
lean_dec(v_a_941_);
lean_dec_ref(v___x_939_);
v___x_980_ = lean_array_push(v_fst_928_, v___x_933_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_980_);
v___x_982_ = v___x_931_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_snd_929_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
v_a_922_ = v___x_982_;
goto v___jp_921_;
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v___x_939_);
lean_dec_ref_known(v___x_933_, 1);
lean_del_object(v___x_931_);
lean_dec(v_snd_929_);
lean_dec(v_fst_928_);
lean_dec(v_a_912_);
lean_dec_ref(v_typeFromIdx_911_);
v_a_984_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_940_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_940_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
}
v___jp_921_:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_nat_add(v_a_912_, v___x_923_);
lean_dec(v_a_912_);
v_a_912_ = v___x_924_;
v_b_913_ = v_a_922_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg___boxed(lean_object* v_upperBound_993_, lean_object* v_args_994_, lean_object* v_typeFromIdx_995_, lean_object* v_a_996_, lean_object* v_b_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v_upperBound_993_, v_args_994_, v_typeFromIdx_995_, v_a_996_, v_b_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec_ref(v_args_994_);
lean_dec(v_upperBound_993_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(lean_object* v_args_1006_, lean_object* v_typeFromIdx_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v___x_1015_; lean_object* v_newArgs_1016_; lean_object* v___x_1017_; lean_object* v_casters_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1015_ = lean_array_get_size(v_args_1006_);
v_newArgs_1016_ = lean_mk_empty_array_with_capacity(v___x_1015_);
v___x_1017_ = lean_unsigned_to_nat(0u);
v_casters_1018_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0));
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v_newArgs_1016_);
lean_ctor_set(v___x_1019_, 1, v_casters_1018_);
v___x_1020_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v___x_1015_, v_args_1006_, v_typeFromIdx_1007_, v___x_1017_, v___x_1019_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1037_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1037_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1037_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v_fst_1025_; lean_object* v_snd_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1036_; 
v_fst_1025_ = lean_ctor_get(v_a_1021_, 0);
v_snd_1026_ = lean_ctor_get(v_a_1021_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_a_1021_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1028_ = v_a_1021_;
v_isShared_1029_ = v_isSharedCheck_1036_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_snd_1026_);
lean_inc(v_fst_1025_);
lean_dec(v_a_1021_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1036_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_fst_1025_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_snd_1026_);
v___x_1031_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1033_; 
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1031_);
v___x_1033_ = v___x_1023_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
else
{
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux___boxed(lean_object* v_args_1038_, lean_object* v_typeFromIdx_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1038_, v_typeFromIdx_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec_ref(v_args_1038_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(lean_object* v_upperBound_1048_, lean_object* v_args_1049_, lean_object* v_typeFromIdx_1050_, lean_object* v_inst_1051_, lean_object* v_R_1052_, lean_object* v_a_1053_, lean_object* v_b_1054_, lean_object* v_c_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v_upperBound_1048_, v_args_1049_, v_typeFromIdx_1050_, v_a_1053_, v_b_1054_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___boxed(lean_object* v_upperBound_1064_, lean_object* v_args_1065_, lean_object* v_typeFromIdx_1066_, lean_object* v_inst_1067_, lean_object* v_R_1068_, lean_object* v_a_1069_, lean_object* v_b_1070_, lean_object* v_c_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(v_upperBound_1064_, v_args_1065_, v_typeFromIdx_1066_, v_inst_1067_, v_R_1068_, v_a_1069_, v_b_1070_, v_c_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec_ref(v_args_1065_);
lean_dec(v_upperBound_1064_);
return v_res_1079_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(lean_object* v_ps_1081_, lean_object* v_i_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v_type_1085_; 
v___x_1083_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0);
v___x_1084_ = lean_array_get_borrowed(v___x_1083_, v_ps_1081_, v_i_1082_);
v_type_1085_ = lean_ctor_get(v___x_1084_, 2);
lean_inc_ref(v_type_1085_);
return v_type_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed(lean_object* v_ps_1086_, lean_object* v_i_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(v_ps_1086_, v_i_1087_);
lean_dec(v_i_1087_);
lean_dec_ref(v_ps_1086_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(lean_object* v_args_1089_, lean_object* v_ps_1090_, lean_object* v_k_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v___f_1099_; lean_object* v___x_1100_; 
v___f_1099_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1099_, 0, v_ps_1090_);
v___x_1100_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1089_, v___f_1099_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v_fst_1102_; lean_object* v_snd_1103_; lean_object* v___x_1104_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v_fst_1102_ = lean_ctor_get(v_a_1101_, 0);
lean_inc(v_fst_1102_);
v_snd_1103_ = lean_ctor_get(v_a_1101_, 1);
lean_inc(v_snd_1103_);
lean_dec(v_a_1101_);
lean_inc(v_a_1097_);
lean_inc_ref(v_a_1096_);
lean_inc(v_a_1095_);
lean_inc_ref(v_a_1094_);
lean_inc(v_a_1093_);
lean_inc_ref(v_a_1092_);
v___x_1104_ = lean_apply_8(v_k_1091_, v_fst_1102_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, lean_box(0));
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1113_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1109_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_1103_, v_a_1105_);
lean_dec(v_snd_1103_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1109_);
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
else
{
lean_dec(v_snd_1103_);
return v___x_1104_;
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec_ref(v_k_1091_);
v_a_1114_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1100_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1100_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___boxed(lean_object* v_args_1122_, lean_object* v_ps_1123_, lean_object* v_k_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(v_args_1122_, v_ps_1123_, v_k_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec_ref(v_args_1122_);
return v_res_1132_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = lean_box(0);
v___x_1137_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1));
v___x_1138_ = l_Lean_Expr_const___override(v___x_1137_, v___x_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(lean_object* v_x_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___boxed(lean_object* v_x_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(v_x_1141_);
lean_dec(v_x_1141_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(lean_object* v_args_1144_, lean_object* v_k_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___f_1153_; lean_object* v___x_1154_; 
v___f_1153_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0));
v___x_1154_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1144_, v___f_1153_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v_fst_1156_; lean_object* v_snd_1157_; lean_object* v___x_1158_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
v_fst_1156_ = lean_ctor_get(v_a_1155_, 0);
lean_inc(v_fst_1156_);
v_snd_1157_ = lean_ctor_get(v_a_1155_, 1);
lean_inc(v_snd_1157_);
lean_dec(v_a_1155_);
lean_inc(v_a_1151_);
lean_inc_ref(v_a_1150_);
lean_inc(v_a_1149_);
lean_inc_ref(v_a_1148_);
lean_inc(v_a_1147_);
lean_inc_ref(v_a_1146_);
v___x_1158_ = lean_apply_8(v_k_1145_, v_fst_1156_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, lean_box(0));
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1167_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1167_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1167_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1163_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_1157_, v_a_1159_);
lean_dec(v_snd_1157_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1163_);
v___x_1165_ = v___x_1161_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
else
{
lean_dec(v_snd_1157_);
return v___x_1158_;
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec_ref(v_k_1145_);
v_a_1168_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1154_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1154_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___boxed(lean_object* v_args_1176_, lean_object* v_k_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(v_args_1176_, v_k_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec_ref(v_args_1176_);
return v_res_1185_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(lean_object* v_msg_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
v___x_1189_ = lean_panic_fn_borrowed(v___x_1188_, v_msg_1187_);
return v___x_1189_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1193_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1194_ = lean_unsigned_to_nat(9u);
v___x_1195_ = lean_unsigned_to_nat(625u);
v___x_1196_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1));
v___x_1197_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0));
v___x_1198_ = l_mkPanicMessageWithDecl(v___x_1197_, v___x_1196_, v___x_1195_, v___x_1194_, v___x_1193_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(lean_object* v_code_1199_, lean_object* v_decl_1200_, lean_object* v_k_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_type_1207_; lean_object* v_value_1208_; uint8_t v___x_1209_; 
v_type_1207_ = lean_ctor_get(v_decl_1200_, 2);
v_value_1208_ = lean_ctor_get(v_decl_1200_, 3);
v___x_1209_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_1207_);
if (v___x_1209_ == 0)
{
if (lean_obj_tag(v_code_1199_) == 0)
{
lean_object* v_decl_1210_; lean_object* v_k_1211_; size_t v___x_1212_; size_t v___x_1213_; uint8_t v___x_1214_; 
v_decl_1210_ = lean_ctor_get(v_code_1199_, 0);
v_k_1211_ = lean_ctor_get(v_code_1199_, 1);
v___x_1212_ = lean_ptr_addr(v_k_1211_);
v___x_1213_ = lean_ptr_addr(v_k_1201_);
v___x_1214_ = lean_usize_dec_eq(v___x_1212_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1222_; 
v_isSharedCheck_1222_ = !lean_is_exclusive(v_code_1199_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; lean_object* v_unused_1224_; 
v_unused_1223_ = lean_ctor_get(v_code_1199_, 1);
lean_dec(v_unused_1223_);
v_unused_1224_ = lean_ctor_get(v_code_1199_, 0);
lean_dec(v_unused_1224_);
v___x_1216_ = v_code_1199_;
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
else
{
lean_dec(v_code_1199_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v_k_1201_);
lean_ctor_set(v___x_1216_, 0, v_decl_1200_);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_decl_1200_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_k_1201_);
v___x_1219_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
}
else
{
size_t v___x_1225_; size_t v___x_1226_; uint8_t v___x_1227_; 
v___x_1225_ = lean_ptr_addr(v_decl_1210_);
v___x_1226_ = lean_ptr_addr(v_decl_1200_);
v___x_1227_ = lean_usize_dec_eq(v___x_1225_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1235_; 
v_isSharedCheck_1235_ = !lean_is_exclusive(v_code_1199_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; lean_object* v_unused_1237_; 
v_unused_1236_ = lean_ctor_get(v_code_1199_, 1);
lean_dec(v_unused_1236_);
v_unused_1237_ = lean_ctor_get(v_code_1199_, 0);
lean_dec(v_unused_1237_);
v___x_1229_ = v_code_1199_;
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
else
{
lean_dec(v_code_1199_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v_k_1201_);
lean_ctor_set(v___x_1229_, 0, v_decl_1200_);
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_decl_1200_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_k_1201_);
v___x_1232_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
}
}
else
{
lean_object* v___x_1238_; 
lean_dec_ref(v_k_1201_);
lean_dec_ref(v_decl_1200_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v_code_1199_);
return v___x_1238_;
}
}
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec_ref(v_k_1201_);
lean_dec_ref(v_decl_1200_);
lean_dec_ref(v_code_1199_);
v___x_1239_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_1240_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
else
{
uint8_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec_ref(v_code_1199_);
v___x_1242_ = 1;
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
lean_inc(v_value_1208_);
v___x_1245_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1242_, v___x_1243_, v___x_1244_, v_value_1208_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v_fvarId_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1245_, 1);
v_fvarId_1247_ = lean_ctor_get(v_a_1246_, 0);
lean_inc(v_fvarId_1247_);
v___x_1248_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_fvarId_1247_);
v___x_1249_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1242_, v_decl_1200_, v___x_1248_, v_a_1203_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1259_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1259_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1259_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_a_1250_);
lean_ctor_set(v___x_1254_, 1, v_k_1201_);
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_a_1246_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1255_);
v___x_1257_ = v___x_1252_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v_a_1246_);
lean_dec_ref(v_k_1201_);
v_a_1260_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1249_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1249_);
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
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v_k_1201_);
lean_dec_ref(v_decl_1200_);
v_a_1268_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1245_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1245_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___boxed(lean_object* v_code_1276_, lean_object* v_decl_1277_, lean_object* v_k_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1276_, v_decl_1277_, v_k_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(lean_object* v_code_1285_, lean_object* v_decl_1286_, lean_object* v_k_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1285_, v_decl_1286_, v_k_1287_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___boxed(lean_object* v_code_1296_, lean_object* v_decl_1297_, lean_object* v_k_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(v_code_1296_, v_decl_1297_, v_k_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(lean_object* v_code_1307_, lean_object* v_decl_1308_, lean_object* v_expType_1309_, lean_object* v_k_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_type_1318_; lean_object* v_value_1319_; uint8_t v___x_1320_; 
v_type_1318_ = lean_ctor_get(v_decl_1308_, 2);
v_value_1319_ = lean_ctor_get(v_decl_1308_, 3);
v___x_1320_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_type_1318_, v_expType_1309_);
if (v___x_1320_ == 0)
{
lean_object* v_boxedTy_1321_; uint8_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec_ref(v_code_1307_);
v_boxedTy_1321_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_1318_);
v___x_1322_ = 1;
v___x_1323_ = lean_box(0);
lean_inc(v_value_1319_);
v___x_1324_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1322_, v___x_1323_, v_boxedTy_1321_, v_value_1319_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v_fvarId_1326_; lean_object* v_type_1327_; lean_object* v___x_1328_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v_fvarId_1326_ = lean_ctor_get(v_a_1325_, 0);
v_type_1327_ = lean_ctor_get(v_a_1325_, 2);
lean_inc_ref(v_type_1318_);
lean_inc_ref(v_type_1327_);
lean_inc(v_fvarId_1326_);
v___x_1328_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_1326_, v_type_1327_, v_type_1318_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1330_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v___x_1330_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1322_, v_decl_1308_, v_a_1329_, v_a_1314_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1340_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1340_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1340_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v_a_1331_);
lean_ctor_set(v___x_1335_, 1, v_k_1310_);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v_a_1325_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1336_);
v___x_1338_ = v___x_1333_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v_a_1325_);
lean_dec_ref(v_k_1310_);
v_a_1341_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1330_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1330_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_a_1325_);
lean_dec_ref(v_k_1310_);
lean_dec_ref(v_decl_1308_);
v_a_1349_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1328_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1328_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref(v_k_1310_);
lean_dec_ref(v_decl_1308_);
v_a_1357_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1324_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1324_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
else
{
if (lean_obj_tag(v_code_1307_) == 0)
{
lean_object* v_decl_1365_; lean_object* v_k_1366_; size_t v___x_1367_; size_t v___x_1368_; uint8_t v___x_1369_; 
v_decl_1365_ = lean_ctor_get(v_code_1307_, 0);
v_k_1366_ = lean_ctor_get(v_code_1307_, 1);
v___x_1367_ = lean_ptr_addr(v_k_1366_);
v___x_1368_ = lean_ptr_addr(v_k_1310_);
v___x_1369_ = lean_usize_dec_eq(v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1377_; 
v_isSharedCheck_1377_ = !lean_is_exclusive(v_code_1307_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; lean_object* v_unused_1379_; 
v_unused_1378_ = lean_ctor_get(v_code_1307_, 1);
lean_dec(v_unused_1378_);
v_unused_1379_ = lean_ctor_get(v_code_1307_, 0);
lean_dec(v_unused_1379_);
v___x_1371_ = v_code_1307_;
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v_code_1307_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v_k_1310_);
lean_ctor_set(v___x_1371_, 0, v_decl_1308_);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_decl_1308_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_k_1310_);
v___x_1374_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
return v___x_1375_;
}
}
}
else
{
size_t v___x_1380_; size_t v___x_1381_; uint8_t v___x_1382_; 
v___x_1380_ = lean_ptr_addr(v_decl_1365_);
v___x_1381_ = lean_ptr_addr(v_decl_1308_);
v___x_1382_ = lean_usize_dec_eq(v___x_1380_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1390_; 
v_isSharedCheck_1390_ = !lean_is_exclusive(v_code_1307_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; lean_object* v_unused_1392_; 
v_unused_1391_ = lean_ctor_get(v_code_1307_, 1);
lean_dec(v_unused_1391_);
v_unused_1392_ = lean_ctor_get(v_code_1307_, 0);
lean_dec(v_unused_1392_);
v___x_1384_ = v_code_1307_;
v_isShared_1385_ = v_isSharedCheck_1390_;
goto v_resetjp_1383_;
}
else
{
lean_dec(v_code_1307_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1390_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 1, v_k_1310_);
lean_ctor_set(v___x_1384_, 0, v_decl_1308_);
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_decl_1308_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_k_1310_);
v___x_1387_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
return v___x_1388_;
}
}
}
else
{
lean_object* v___x_1393_; 
lean_dec_ref(v_k_1310_);
lean_dec_ref(v_decl_1308_);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_code_1307_);
return v___x_1393_;
}
}
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec_ref(v_k_1310_);
lean_dec_ref(v_decl_1308_);
lean_dec_ref(v_code_1307_);
v___x_1394_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_1395_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_1394_);
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
return v___x_1396_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded___boxed(lean_object* v_code_1397_, lean_object* v_decl_1398_, lean_object* v_expType_1399_, lean_object* v_k_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(v_code_1397_, v_decl_1398_, v_expType_1399_, v_k_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec_ref(v_expType_1399_);
return v_res_1408_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_instMonadEIO___redArg();
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(lean_object* v_msg_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v_toApplicative_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1487_; 
v___x_1422_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
v___x_1423_ = l_StateRefT_x27_instMonad___redArg(v___x_1422_);
v_toApplicative_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; 
v_unused_1488_ = lean_ctor_get(v___x_1423_, 1);
lean_dec(v_unused_1488_);
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1487_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_toApplicative_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1487_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v_toFunctor_1428_; lean_object* v_toSeq_1429_; lean_object* v_toSeqLeft_1430_; lean_object* v_toSeqRight_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1485_; 
v_toFunctor_1428_ = lean_ctor_get(v_toApplicative_1424_, 0);
v_toSeq_1429_ = lean_ctor_get(v_toApplicative_1424_, 2);
v_toSeqLeft_1430_ = lean_ctor_get(v_toApplicative_1424_, 3);
v_toSeqRight_1431_ = lean_ctor_get(v_toApplicative_1424_, 4);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_toApplicative_1424_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; 
v_unused_1486_ = lean_ctor_get(v_toApplicative_1424_, 1);
lean_dec(v_unused_1486_);
v___x_1433_ = v_toApplicative_1424_;
v_isShared_1434_ = v_isSharedCheck_1485_;
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
v_isShared_1434_ = v_isSharedCheck_1485_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___f_1435_; lean_object* v___f_1436_; lean_object* v___f_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___x_1444_; 
v___f_1435_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1));
v___f_1436_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2));
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
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v___f_1435_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v___f_1442_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v___f_1441_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v___f_1440_);
v___x_1444_ = v_reuseFailAlloc_1484_;
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
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v___f_1436_);
v___x_1446_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v_toApplicative_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1481_; 
v___x_1447_ = l_StateRefT_x27_instMonad___redArg(v___x_1446_);
v_toApplicative_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v___x_1447_, 1);
lean_dec(v_unused_1482_);
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1481_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_toApplicative_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1481_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v_toFunctor_1452_; lean_object* v_toSeq_1453_; lean_object* v_toSeqLeft_1454_; lean_object* v_toSeqRight_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1479_; 
v_toFunctor_1452_ = lean_ctor_get(v_toApplicative_1448_, 0);
v_toSeq_1453_ = lean_ctor_get(v_toApplicative_1448_, 2);
v_toSeqLeft_1454_ = lean_ctor_get(v_toApplicative_1448_, 3);
v_toSeqRight_1455_ = lean_ctor_get(v_toApplicative_1448_, 4);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_toApplicative_1448_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; 
v_unused_1480_ = lean_ctor_get(v_toApplicative_1448_, 1);
lean_dec(v_unused_1480_);
v___x_1457_ = v_toApplicative_1448_;
v_isShared_1458_ = v_isSharedCheck_1479_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_toSeqRight_1455_);
lean_inc(v_toSeqLeft_1454_);
lean_inc(v_toSeq_1453_);
lean_inc(v_toFunctor_1452_);
lean_dec(v_toApplicative_1448_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1479_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___f_1459_; lean_object* v___f_1460_; lean_object* v___f_1461_; lean_object* v___f_1462_; lean_object* v___x_1463_; lean_object* v___f_1464_; lean_object* v___f_1465_; lean_object* v___f_1466_; lean_object* v___x_1468_; 
v___f_1459_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3));
v___f_1460_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1452_);
v___f_1461_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1461_, 0, v_toFunctor_1452_);
v___f_1462_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1462_, 0, v_toFunctor_1452_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___f_1461_);
lean_ctor_set(v___x_1463_, 1, v___f_1462_);
v___f_1464_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1464_, 0, v_toSeqRight_1455_);
v___f_1465_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1465_, 0, v_toSeqLeft_1454_);
v___f_1466_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1466_, 0, v_toSeq_1453_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v___f_1464_);
lean_ctor_set(v___x_1457_, 3, v___f_1465_);
lean_ctor_set(v___x_1457_, 2, v___f_1466_);
lean_ctor_set(v___x_1457_, 1, v___f_1459_);
lean_ctor_set(v___x_1457_, 0, v___x_1463_);
v___x_1468_ = v___x_1457_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v___f_1459_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v___f_1466_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v___f_1465_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v___f_1464_);
v___x_1468_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1470_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 1, v___f_1460_);
lean_ctor_set(v___x_1450_, 0, v___x_1468_);
v___x_1470_ = v___x_1450_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v___f_1460_);
v___x_1470_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___f_1474_; lean_object* v___x_2578__overap_1475_; lean_object* v___x_1476_; 
v___x_1471_ = l_StateRefT_x27_instMonad___redArg(v___x_1470_);
v___x_1472_ = l_Lean_instInhabitedExpr;
v___x_1473_ = l_instInhabitedOfMonad___redArg(v___x_1471_, v___x_1472_);
v___f_1474_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1474_, 0, v___x_1473_);
v___x_2578__overap_1475_ = lean_panic_fn_borrowed(v___f_1474_, v_msg_1414_);
lean_dec_ref(v___f_1474_);
lean_inc(v___y_1420_);
lean_inc_ref(v___y_1419_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
lean_inc(v___y_1416_);
lean_inc_ref(v___y_1415_);
v___x_1476_ = lean_apply_7(v___x_2578__overap_1475_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, lean_box(0));
return v___x_1476_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___boxed(lean_object* v_msg_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v_msg_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
return v_res_1497_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1500_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1501_ = lean_unsigned_to_nat(44u);
v___x_1502_ = lean_unsigned_to_nat(316u);
v___x_1503_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1));
v___x_1504_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1505_ = l_mkPanicMessageWithDecl(v___x_1504_, v___x_1503_, v___x_1502_, v___x_1501_, v___x_1500_);
return v___x_1505_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_box(0);
v___x_1510_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4));
v___x_1511_ = l_Lean_Expr_const___override(v___x_1510_, v___x_1509_);
return v___x_1511_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = lean_box(0);
v___x_1516_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7));
v___x_1517_ = l_Lean_Expr_const___override(v___x_1516_, v___x_1515_);
return v___x_1517_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = lean_box(0);
v___x_1522_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10));
v___x_1523_ = l_Lean_Expr_const___override(v___x_1522_, v___x_1521_);
return v___x_1523_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1524_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1525_ = lean_unsigned_to_nat(45u);
v___x_1526_ = lean_unsigned_to_nat(301u);
v___x_1527_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1));
v___x_1528_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1529_ = l_mkPanicMessageWithDecl(v___x_1528_, v___x_1527_, v___x_1526_, v___x_1525_, v___x_1524_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(lean_object* v_currentType_1530_, lean_object* v_value_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; 
switch(lean_obj_tag(v_value_1531_))
{
case 0:
{
lean_object* v_value_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1578_; 
v_value_1548_ = lean_ctor_get(v_value_1531_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_value_1531_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1550_ = v_value_1531_;
v_isShared_1551_ = v_isSharedCheck_1578_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_value_1548_);
lean_dec(v_value_1531_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1578_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
switch(lean_obj_tag(v_value_1548_))
{
case 0:
{
lean_object* v_val_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1565_; 
lean_del_object(v___x_1550_);
v_val_1552_ = lean_ctor_get(v_value_1548_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_value_1548_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1554_ = v_value_1548_;
v_isShared_1555_ = v_isSharedCheck_1565_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_val_1552_);
lean_dec(v_value_1548_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1565_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1556_ = l_Lean_maxSmallNat;
v___x_1557_ = lean_nat_dec_le(v_val_1552_, v___x_1556_);
lean_dec(v_val_1552_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1559_; 
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v_currentType_1530_);
v___x_1559_ = v___x_1554_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_currentType_1530_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
lean_dec_ref(v_currentType_1530_);
v___x_1561_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1561_);
v___x_1563_ = v___x_1554_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
case 1:
{
lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1573_; 
lean_del_object(v___x_1550_);
lean_dec_ref(v_currentType_1530_);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_value_1548_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v_value_1548_, 0);
lean_dec(v_unused_1574_);
v___x_1567_ = v_value_1548_;
v_isShared_1568_ = v_isSharedCheck_1573_;
goto v_resetjp_1566_;
}
else
{
lean_dec(v_value_1548_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1573_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1569_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
if (v_isShared_1568_ == 0)
{
lean_ctor_set_tag(v___x_1567_, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1569_);
v___x_1571_ = v___x_1567_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
default: 
{
lean_object* v___x_1576_; 
lean_dec_ref(v_value_1548_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v_currentType_1530_);
v___x_1576_ = v___x_1550_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_currentType_1530_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec_ref(v_currentType_1530_);
v___x_1579_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
return v___x_1580_;
}
case 5:
{
lean_object* v_i_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec_ref(v_currentType_1530_);
v_i_1581_ = lean_ctor_get(v_value_1531_, 0);
lean_inc_ref(v_i_1581_);
lean_dec_ref_known(v_value_1531_, 2);
v___x_1582_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_i_1581_);
lean_dec_ref(v_i_1581_);
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
return v___x_1583_;
}
case 7:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec_ref_known(v_value_1531_, 2);
lean_dec_ref(v_currentType_1530_);
v___x_1584_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
case 9:
{
lean_object* v_fn_1586_; lean_object* v___x_1587_; 
lean_dec_ref(v_currentType_1530_);
v_fn_1586_ = lean_ctor_get(v_value_1531_, 0);
lean_inc(v_fn_1586_);
lean_dec_ref_known(v_value_1531_, 2);
v___x_1587_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_1586_, v_a_1537_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1599_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1599_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1599_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
if (lean_obj_tag(v_a_1588_) == 1)
{
lean_object* v_val_1592_; lean_object* v_type_1593_; lean_object* v___x_1595_; 
v_val_1592_ = lean_ctor_get(v_a_1588_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v_a_1588_, 1);
v_type_1593_ = lean_ctor_get(v_val_1592_, 2);
lean_inc_ref(v_type_1593_);
lean_dec(v_val_1592_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v_type_1593_);
v___x_1595_ = v___x_1590_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_type_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_del_object(v___x_1590_);
lean_dec(v_a_1588_);
v___x_1597_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12);
v___x_1598_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1597_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
return v___x_1598_;
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_a_1600_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1587_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1587_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
case 10:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec_ref_known(v_value_1531_, 2);
lean_dec_ref(v_currentType_1530_);
v___x_1608_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
return v___x_1609_;
}
case 13:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec_ref_known(v_value_1531_, 2);
lean_dec_ref(v_currentType_1530_);
v___x_1610_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
v___x_1611_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1610_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
return v___x_1611_;
}
case 14:
{
lean_dec_ref_known(v_value_1531_, 1);
lean_dec_ref(v_currentType_1530_);
v___y_1540_ = v_a_1532_;
v___y_1541_ = v_a_1533_;
v___y_1542_ = v_a_1534_;
v___y_1543_ = v_a_1535_;
v___y_1544_ = v_a_1536_;
v___y_1545_ = v_a_1537_;
goto v___jp_1539_;
}
case 15:
{
lean_dec_ref_known(v_value_1531_, 1);
lean_dec_ref(v_currentType_1530_);
v___y_1540_ = v_a_1532_;
v___y_1541_ = v_a_1533_;
v___y_1542_ = v_a_1534_;
v___y_1543_ = v_a_1535_;
v___y_1544_ = v_a_1536_;
v___y_1545_ = v_a_1537_;
goto v___jp_1539_;
}
default: 
{
lean_object* v___x_1612_; 
lean_dec(v_value_1531_);
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v_currentType_1530_);
return v___x_1612_;
}
}
v___jp_1539_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
v___x_1547_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1546_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___boxed(lean_object* v_currentType_1613_, lean_object* v_value_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(v_currentType_1613_, v_value_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(lean_object* v_msg_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_toApplicative_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1696_; 
v___x_1631_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
v___x_1632_ = l_StateRefT_x27_instMonad___redArg(v___x_1631_);
v_toApplicative_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; 
v_unused_1697_ = lean_ctor_get(v___x_1632_, 1);
lean_dec(v_unused_1697_);
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1696_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_toApplicative_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1696_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v_toFunctor_1637_; lean_object* v_toSeq_1638_; lean_object* v_toSeqLeft_1639_; lean_object* v_toSeqRight_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1694_; 
v_toFunctor_1637_ = lean_ctor_get(v_toApplicative_1633_, 0);
v_toSeq_1638_ = lean_ctor_get(v_toApplicative_1633_, 2);
v_toSeqLeft_1639_ = lean_ctor_get(v_toApplicative_1633_, 3);
v_toSeqRight_1640_ = lean_ctor_get(v_toApplicative_1633_, 4);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_toApplicative_1633_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v_toApplicative_1633_, 1);
lean_dec(v_unused_1695_);
v___x_1642_ = v_toApplicative_1633_;
v_isShared_1643_ = v_isSharedCheck_1694_;
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
v_isShared_1643_ = v_isSharedCheck_1694_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___f_1644_; lean_object* v___f_1645_; lean_object* v___f_1646_; lean_object* v___f_1647_; lean_object* v___x_1648_; lean_object* v___f_1649_; lean_object* v___f_1650_; lean_object* v___f_1651_; lean_object* v___x_1653_; 
v___f_1644_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1));
v___f_1645_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2));
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
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___f_1644_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v___f_1651_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v___f_1650_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v___f_1649_);
v___x_1653_ = v_reuseFailAlloc_1693_;
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
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___f_1645_);
v___x_1655_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; lean_object* v_toApplicative_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1690_; 
v___x_1656_ = l_StateRefT_x27_instMonad___redArg(v___x_1655_);
v_toApplicative_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v___x_1656_, 1);
lean_dec(v_unused_1691_);
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1690_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_toApplicative_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1690_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v_toFunctor_1661_; lean_object* v_toSeq_1662_; lean_object* v_toSeqLeft_1663_; lean_object* v_toSeqRight_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1688_; 
v_toFunctor_1661_ = lean_ctor_get(v_toApplicative_1657_, 0);
v_toSeq_1662_ = lean_ctor_get(v_toApplicative_1657_, 2);
v_toSeqLeft_1663_ = lean_ctor_get(v_toApplicative_1657_, 3);
v_toSeqRight_1664_ = lean_ctor_get(v_toApplicative_1657_, 4);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_toApplicative_1657_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v_toApplicative_1657_, 1);
lean_dec(v_unused_1689_);
v___x_1666_ = v_toApplicative_1657_;
v_isShared_1667_ = v_isSharedCheck_1688_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_toSeqRight_1664_);
lean_inc(v_toSeqLeft_1663_);
lean_inc(v_toSeq_1662_);
lean_inc(v_toFunctor_1661_);
lean_dec(v_toApplicative_1657_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1688_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___f_1668_; lean_object* v___f_1669_; lean_object* v___f_1670_; lean_object* v___f_1671_; lean_object* v___x_1672_; lean_object* v___f_1673_; lean_object* v___f_1674_; lean_object* v___f_1675_; lean_object* v___x_1677_; 
v___f_1668_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3));
v___f_1669_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1661_);
v___f_1670_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1670_, 0, v_toFunctor_1661_);
v___f_1671_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1671_, 0, v_toFunctor_1661_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___f_1670_);
lean_ctor_set(v___x_1672_, 1, v___f_1671_);
v___f_1673_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1673_, 0, v_toSeqRight_1664_);
v___f_1674_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1674_, 0, v_toSeqLeft_1663_);
v___f_1675_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1675_, 0, v_toSeq_1662_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 4, v___f_1673_);
lean_ctor_set(v___x_1666_, 3, v___f_1674_);
lean_ctor_set(v___x_1666_, 2, v___f_1675_);
lean_ctor_set(v___x_1666_, 1, v___f_1668_);
lean_ctor_set(v___x_1666_, 0, v___x_1672_);
v___x_1677_ = v___x_1666_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___f_1668_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v___f_1675_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v___f_1674_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v___f_1673_);
v___x_1677_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1679_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v___f_1669_);
lean_ctor_set(v___x_1659_, 0, v___x_1677_);
v___x_1679_ = v___x_1659_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v___f_1669_);
v___x_1679_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___f_1683_; lean_object* v___x_22117__overap_1684_; lean_object* v___x_1685_; 
v___x_1680_ = l_StateRefT_x27_instMonad___redArg(v___x_1679_);
v___x_1681_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
v___x_1682_ = l_instInhabitedOfMonad___redArg(v___x_1680_, v___x_1681_);
v___f_1683_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1683_, 0, v___x_1682_);
v___x_22117__overap_1684_ = lean_panic_fn_borrowed(v___f_1683_, v_msg_1623_);
lean_dec_ref(v___f_1683_);
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
lean_inc(v___y_1627_);
lean_inc_ref(v___y_1626_);
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
v___x_1685_ = lean_apply_7(v___x_22117__overap_1684_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, lean_box(0));
return v___x_1685_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0___boxed(lean_object* v_msg_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v_msg_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(lean_object* v_x_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0___boxed(lean_object* v_x_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(v_x_1709_);
lean_dec(v_x_1709_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4(lean_object* v_params_1711_, lean_object* v_i_1712_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v_type_1715_; 
v___x_1713_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0);
v___x_1714_ = lean_array_get_borrowed(v___x_1713_, v_params_1711_, v_i_1712_);
v_type_1715_ = lean_ctor_get(v___x_1714_, 2);
lean_inc_ref(v_type_1715_);
return v_type_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4___boxed(lean_object* v_params_1716_, lean_object* v_i_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4(v_params_1716_, v_i_1717_);
lean_dec(v_i_1717_);
lean_dec_ref(v_params_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(lean_object* v_fvarId_1719_, lean_object* v_code_1720_, lean_object* v_fvarId_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
uint8_t v___x_1729_; 
v___x_1729_ = l_Lean_instBEqFVarId_beq(v_fvarId_1719_, v_fvarId_1721_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec_ref(v_code_1720_);
v___x_1730_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_fvarId_1721_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; 
lean_dec(v_fvarId_1721_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_code_1720_);
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2___boxed(lean_object* v_fvarId_1733_, lean_object* v_code_1734_, lean_object* v_fvarId_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_1733_, v_code_1734_, v_fvarId_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v_fvarId_1733_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(lean_object* v_typeName_1744_, lean_object* v_a_1745_, lean_object* v_alts_1746_, lean_object* v_resultType_1747_, lean_object* v_discr_1748_, lean_object* v_code_1749_, lean_object* v_discr_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_currDeclResultType_1758_; size_t v___x_1763_; size_t v___x_1764_; uint8_t v___x_1765_; 
v_currDeclResultType_1758_ = lean_ctor_get(v___y_1751_, 1);
v___x_1763_ = lean_ptr_addr(v_alts_1746_);
v___x_1764_ = lean_ptr_addr(v_a_1745_);
v___x_1765_ = lean_usize_dec_eq(v___x_1763_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_dec_ref(v_code_1749_);
goto v___jp_1759_;
}
else
{
size_t v___x_1766_; size_t v___x_1767_; uint8_t v___x_1768_; 
v___x_1766_ = lean_ptr_addr(v_resultType_1747_);
v___x_1767_ = lean_ptr_addr(v_currDeclResultType_1758_);
v___x_1768_ = lean_usize_dec_eq(v___x_1766_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_dec_ref(v_code_1749_);
goto v___jp_1759_;
}
else
{
uint8_t v___x_1769_; 
v___x_1769_ = l_Lean_instBEqFVarId_beq(v_discr_1748_, v_discr_1750_);
if (v___x_1769_ == 0)
{
lean_dec_ref(v_code_1749_);
goto v___jp_1759_;
}
else
{
lean_object* v___x_1770_; 
lean_dec(v_discr_1750_);
lean_dec_ref(v_a_1745_);
lean_dec(v_typeName_1744_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_code_1749_);
return v___x_1770_;
}
}
}
v___jp_1759_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_inc_ref(v_currDeclResultType_1758_);
v___x_1760_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1760_, 0, v_typeName_1744_);
lean_ctor_set(v___x_1760_, 1, v_currDeclResultType_1758_);
lean_ctor_set(v___x_1760_, 2, v_discr_1750_);
lean_ctor_set(v___x_1760_, 3, v_a_1745_);
v___x_1761_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1___boxed(lean_object* v_typeName_1771_, lean_object* v_a_1772_, lean_object* v_alts_1773_, lean_object* v_resultType_1774_, lean_object* v_discr_1775_, lean_object* v_code_1776_, lean_object* v_discr_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_1771_, v_a_1772_, v_alts_1773_, v_resultType_1774_, v_discr_1775_, v_code_1776_, v_discr_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v_discr_1775_);
lean_dec_ref(v_resultType_1774_);
lean_dec_ref(v_alts_1773_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(lean_object* v_alt_1786_, lean_object* v_f_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___y_1796_; 
switch(lean_obj_tag(v_alt_1786_))
{
case 0:
{
lean_object* v_code_1815_; 
v_code_1815_ = lean_ctor_get(v_alt_1786_, 2);
lean_inc_ref(v_code_1815_);
v___y_1796_ = v_code_1815_;
goto v___jp_1795_;
}
case 1:
{
lean_object* v_code_1816_; 
v_code_1816_ = lean_ctor_get(v_alt_1786_, 1);
lean_inc_ref(v_code_1816_);
v___y_1796_ = v_code_1816_;
goto v___jp_1795_;
}
default: 
{
lean_object* v_code_1817_; 
v_code_1817_ = lean_ctor_get(v_alt_1786_, 0);
lean_inc_ref(v_code_1817_);
v___y_1796_ = v_code_1817_;
goto v___jp_1795_;
}
}
v___jp_1795_:
{
lean_object* v___x_1797_; 
lean_inc(v___y_1793_);
lean_inc_ref(v___y_1792_);
lean_inc(v___y_1791_);
lean_inc_ref(v___y_1790_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1788_);
v___x_1797_ = lean_apply_8(v_f_1787_, v___y_1796_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, lean_box(0));
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1806_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1786_, v_a_1798_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec_ref(v_alt_1786_);
v_a_1807_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1797_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1797_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg___boxed(lean_object* v_alt_1818_, lean_object* v_f_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_alt_1818_, v_f_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(lean_object* v_fvarId_1828_, lean_object* v_i_1829_, lean_object* v_offset_1830_, lean_object* v_ty_1831_, lean_object* v_a_1832_, lean_object* v_y_1833_, lean_object* v_k_1834_, lean_object* v_code_1835_, lean_object* v_y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
size_t v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = lean_ptr_addr(v_fvarId_1828_);
v___x_1845_ = lean_usize_dec_eq(v___x_1844_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_dec_ref(v_code_1835_);
v___x_1846_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1846_, 0, v_fvarId_1828_);
lean_ctor_set(v___x_1846_, 1, v_i_1829_);
lean_ctor_set(v___x_1846_, 2, v_offset_1830_);
lean_ctor_set(v___x_1846_, 3, v_y_1836_);
lean_ctor_set(v___x_1846_, 4, v_ty_1831_);
lean_ctor_set(v___x_1846_, 5, v_a_1832_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
else
{
uint8_t v___x_1848_; 
v___x_1848_ = lean_nat_dec_eq(v_i_1829_, v_i_1829_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
lean_dec_ref(v_code_1835_);
v___x_1849_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1849_, 0, v_fvarId_1828_);
lean_ctor_set(v___x_1849_, 1, v_i_1829_);
lean_ctor_set(v___x_1849_, 2, v_offset_1830_);
lean_ctor_set(v___x_1849_, 3, v_y_1836_);
lean_ctor_set(v___x_1849_, 4, v_ty_1831_);
lean_ctor_set(v___x_1849_, 5, v_a_1832_);
v___x_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
return v___x_1850_;
}
else
{
uint8_t v___x_1851_; 
v___x_1851_ = lean_nat_dec_eq(v_offset_1830_, v_offset_1830_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec_ref(v_code_1835_);
v___x_1852_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1852_, 0, v_fvarId_1828_);
lean_ctor_set(v___x_1852_, 1, v_i_1829_);
lean_ctor_set(v___x_1852_, 2, v_offset_1830_);
lean_ctor_set(v___x_1852_, 3, v_y_1836_);
lean_ctor_set(v___x_1852_, 4, v_ty_1831_);
lean_ctor_set(v___x_1852_, 5, v_a_1832_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
else
{
size_t v___x_1854_; size_t v___x_1855_; uint8_t v___x_1856_; 
v___x_1854_ = lean_ptr_addr(v_y_1833_);
v___x_1855_ = lean_ptr_addr(v_y_1836_);
v___x_1856_ = lean_usize_dec_eq(v___x_1854_, v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
lean_dec_ref(v_code_1835_);
v___x_1857_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1857_, 0, v_fvarId_1828_);
lean_ctor_set(v___x_1857_, 1, v_i_1829_);
lean_ctor_set(v___x_1857_, 2, v_offset_1830_);
lean_ctor_set(v___x_1857_, 3, v_y_1836_);
lean_ctor_set(v___x_1857_, 4, v_ty_1831_);
lean_ctor_set(v___x_1857_, 5, v_a_1832_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
else
{
size_t v___x_1859_; uint8_t v___x_1860_; 
v___x_1859_ = lean_ptr_addr(v_ty_1831_);
v___x_1860_ = lean_usize_dec_eq(v___x_1859_, v___x_1859_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_dec_ref(v_code_1835_);
v___x_1861_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1861_, 0, v_fvarId_1828_);
lean_ctor_set(v___x_1861_, 1, v_i_1829_);
lean_ctor_set(v___x_1861_, 2, v_offset_1830_);
lean_ctor_set(v___x_1861_, 3, v_y_1836_);
lean_ctor_set(v___x_1861_, 4, v_ty_1831_);
lean_ctor_set(v___x_1861_, 5, v_a_1832_);
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
return v___x_1862_;
}
else
{
size_t v___x_1863_; size_t v___x_1864_; uint8_t v___x_1865_; 
v___x_1863_ = lean_ptr_addr(v_k_1834_);
v___x_1864_ = lean_ptr_addr(v_a_1832_);
v___x_1865_ = lean_usize_dec_eq(v___x_1863_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_dec_ref(v_code_1835_);
v___x_1866_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1866_, 0, v_fvarId_1828_);
lean_ctor_set(v___x_1866_, 1, v_i_1829_);
lean_ctor_set(v___x_1866_, 2, v_offset_1830_);
lean_ctor_set(v___x_1866_, 3, v_y_1836_);
lean_ctor_set(v___x_1866_, 4, v_ty_1831_);
lean_ctor_set(v___x_1866_, 5, v_a_1832_);
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; 
lean_dec(v_y_1836_);
lean_dec_ref(v_a_1832_);
lean_dec_ref(v_ty_1831_);
lean_dec(v_offset_1830_);
lean_dec(v_i_1829_);
lean_dec(v_fvarId_1828_);
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_code_1835_);
return v___x_1868_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4___boxed(lean_object* v_fvarId_1869_, lean_object* v_i_1870_, lean_object* v_offset_1871_, lean_object* v_ty_1872_, lean_object* v_a_1873_, lean_object* v_y_1874_, lean_object* v_k_1875_, lean_object* v_code_1876_, lean_object* v_y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_1869_, v_i_1870_, v_offset_1871_, v_ty_1872_, v_a_1873_, v_y_1874_, v_k_1875_, v_code_1876_, v_y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec_ref(v_k_1875_);
lean_dec(v_y_1874_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(lean_object* v_fvarId_1886_, lean_object* v_i_1887_, lean_object* v_a_1888_, lean_object* v_y_1889_, lean_object* v_k_1890_, lean_object* v_code_1891_, lean_object* v_y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
size_t v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = lean_ptr_addr(v_fvarId_1886_);
v___x_1901_ = lean_usize_dec_eq(v___x_1900_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec_ref(v_code_1891_);
v___x_1902_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1902_, 0, v_fvarId_1886_);
lean_ctor_set(v___x_1902_, 1, v_i_1887_);
lean_ctor_set(v___x_1902_, 2, v_y_1892_);
lean_ctor_set(v___x_1902_, 3, v_a_1888_);
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
else
{
uint8_t v___x_1904_; 
v___x_1904_ = lean_nat_dec_eq(v_i_1887_, v_i_1887_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_dec_ref(v_code_1891_);
v___x_1905_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1905_, 0, v_fvarId_1886_);
lean_ctor_set(v___x_1905_, 1, v_i_1887_);
lean_ctor_set(v___x_1905_, 2, v_y_1892_);
lean_ctor_set(v___x_1905_, 3, v_a_1888_);
v___x_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
return v___x_1906_;
}
else
{
size_t v___x_1907_; size_t v___x_1908_; uint8_t v___x_1909_; 
v___x_1907_ = lean_ptr_addr(v_y_1889_);
v___x_1908_ = lean_ptr_addr(v_y_1892_);
v___x_1909_ = lean_usize_dec_eq(v___x_1907_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
lean_dec_ref(v_code_1891_);
v___x_1910_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1910_, 0, v_fvarId_1886_);
lean_ctor_set(v___x_1910_, 1, v_i_1887_);
lean_ctor_set(v___x_1910_, 2, v_y_1892_);
lean_ctor_set(v___x_1910_, 3, v_a_1888_);
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
return v___x_1911_;
}
else
{
size_t v___x_1912_; size_t v___x_1913_; uint8_t v___x_1914_; 
v___x_1912_ = lean_ptr_addr(v_k_1890_);
v___x_1913_ = lean_ptr_addr(v_a_1888_);
v___x_1914_ = lean_usize_dec_eq(v___x_1912_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_dec_ref(v_code_1891_);
v___x_1915_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1915_, 0, v_fvarId_1886_);
lean_ctor_set(v___x_1915_, 1, v_i_1887_);
lean_ctor_set(v___x_1915_, 2, v_y_1892_);
lean_ctor_set(v___x_1915_, 3, v_a_1888_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
return v___x_1916_;
}
else
{
lean_object* v___x_1917_; 
lean_dec(v_y_1892_);
lean_dec_ref(v_a_1888_);
lean_dec(v_i_1887_);
lean_dec(v_fvarId_1886_);
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_code_1891_);
return v___x_1917_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3___boxed(lean_object* v_fvarId_1918_, lean_object* v_i_1919_, lean_object* v_a_1920_, lean_object* v_y_1921_, lean_object* v_k_1922_, lean_object* v_code_1923_, lean_object* v_y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_1918_, v_i_1919_, v_a_1920_, v_y_1921_, v_k_1922_, v_code_1923_, v_y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec_ref(v_k_1922_);
lean_dec(v_y_1921_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(lean_object* v_params_1933_, lean_object* v_i_1934_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v_type_1937_; 
v___x_1935_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0);
v___x_1936_ = lean_array_get_borrowed(v___x_1935_, v_params_1933_, v_i_1934_);
v_type_1937_ = lean_ctor_get(v___x_1936_, 2);
lean_inc_ref(v_type_1937_);
return v_type_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed(lean_object* v_params_1938_, lean_object* v_i_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(v_params_1938_, v_i_1939_);
lean_dec(v_i_1939_);
lean_dec_ref(v_params_1938_);
return v_res_1940_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1942_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1943_ = lean_unsigned_to_nat(44u);
v___x_1944_ = lean_unsigned_to_nat(353u);
v___x_1945_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_1946_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1947_ = l_mkPanicMessageWithDecl(v___x_1946_, v___x_1945_, v___x_1944_, v___x_1943_, v___x_1942_);
return v___x_1947_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1949_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1950_ = lean_unsigned_to_nat(45u);
v___x_1951_ = lean_unsigned_to_nat(336u);
v___x_1952_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_1953_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1954_ = l_mkPanicMessageWithDecl(v___x_1953_, v___x_1952_, v___x_1951_, v___x_1950_, v___x_1949_);
return v___x_1954_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4(void){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1955_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1956_ = lean_unsigned_to_nat(45u);
v___x_1957_ = lean_unsigned_to_nat(341u);
v___x_1958_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_1959_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1960_ = l_mkPanicMessageWithDecl(v___x_1959_, v___x_1958_, v___x_1957_, v___x_1956_, v___x_1955_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(lean_object* v_code_1961_, lean_object* v_decl_1962_, lean_object* v_k_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v_type_1990_; lean_object* v_value_1991_; lean_object* v___f_1992_; lean_object* v___x_1993_; 
v_type_1990_ = lean_ctor_get(v_decl_1962_, 2);
v_value_1991_ = lean_ctor_get(v_decl_1962_, 3);
lean_inc_n(v_value_1991_, 2);
v___f_1992_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2));
lean_inc_ref(v_type_1990_);
v___x_1993_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(v_type_1990_, v_value_1991_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; uint8_t v___x_1995_; lean_object* v___x_1996_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc_n(v_a_1994_, 2);
lean_dec_ref_known(v___x_1993_, 1);
v___x_1995_ = 1;
v___x_1996_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_1995_, v_decl_1962_, v_a_1994_, v_value_1991_, v_a_1967_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v___x_1998_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2473_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2473_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2473_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_value_2003_; lean_object* v___y_2005_; 
v_value_2003_ = lean_ctor_get(v_a_1997_, 3);
switch(lean_obj_tag(v_value_2003_))
{
case 4:
{
lean_object* v_args_2065_; lean_object* v___x_2066_; 
lean_del_object(v___x_2001_);
lean_dec(v_a_1994_);
v_args_2065_ = lean_ctor_get(v_value_2003_, 1);
v___x_2066_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2065_, v___f_1992_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
v_fst_2068_ = lean_ctor_get(v_a_2067_, 0);
lean_inc(v_fst_2068_);
v_snd_2069_ = lean_ctor_get(v_a_2067_, 1);
lean_inc(v_snd_2069_);
lean_dec(v_a_2067_);
lean_inc_ref(v_value_2003_);
v___x_2070_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_value_2003_, v_fst_2068_);
v___x_2071_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1995_, v_a_1997_, v___x_2070_, v_a_1967_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2073_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v___x_2071_, 1);
v___x_2073_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1961_, v_a_2072_, v_a_1999_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2082_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_2069_, v_a_2074_);
lean_dec(v_snd_2069_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2078_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
else
{
lean_dec(v_snd_2069_);
return v___x_2073_;
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_snd_2069_);
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v_a_2083_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2071_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2071_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec_ref(v_code_1961_);
v_a_2091_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2066_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2066_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
case 5:
{
lean_object* v_i_2099_; lean_object* v_args_2100_; uint8_t v___x_2153_; 
v_i_2099_ = lean_ctor_get(v_value_2003_, 0);
v_args_2100_ = lean_ctor_get(v_value_2003_, 1);
v___x_2153_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_i_2099_);
if (v___x_2153_ == 0)
{
lean_del_object(v___x_2001_);
lean_dec(v_a_1994_);
goto v___jp_2101_;
}
else
{
uint8_t v___x_2154_; 
v___x_2154_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_1994_);
if (v___x_2154_ == 0)
{
lean_del_object(v___x_2001_);
lean_dec(v_a_1994_);
goto v___jp_2101_;
}
else
{
lean_object* v_cidx_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v_cidx_2155_ = lean_ctor_get(v_i_2099_, 1);
v___x_2156_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_1994_, v_cidx_2155_);
lean_dec(v_a_1994_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2156_);
v___x_2158_ = v___x_2001_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1995_, v_a_1997_, v___x_2158_, v_a_1967_);
if (lean_obj_tag(v___x_2159_) == 0)
{
if (lean_obj_tag(v_code_1961_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2199_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2199_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2199_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_decl_2164_; lean_object* v_k_2165_; size_t v___x_2166_; size_t v___x_2167_; uint8_t v___x_2168_; 
v_decl_2164_ = lean_ctor_get(v_code_1961_, 0);
v_k_2165_ = lean_ctor_get(v_code_1961_, 1);
v___x_2166_ = lean_ptr_addr(v_k_2165_);
v___x_2167_ = lean_ptr_addr(v_a_1999_);
v___x_2168_ = lean_usize_dec_eq(v___x_2166_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2178_; 
v_isSharedCheck_2178_ = !lean_is_exclusive(v_code_1961_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; lean_object* v_unused_2180_; 
v_unused_2179_ = lean_ctor_get(v_code_1961_, 1);
lean_dec(v_unused_2179_);
v_unused_2180_ = lean_ctor_get(v_code_1961_, 0);
lean_dec(v_unused_2180_);
v___x_2170_ = v_code_1961_;
v_isShared_2171_ = v_isSharedCheck_2178_;
goto v_resetjp_2169_;
}
else
{
lean_dec(v_code_1961_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2178_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 1, v_a_1999_);
lean_ctor_set(v___x_2170_, 0, v_a_2160_);
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2160_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_a_1999_);
v___x_2173_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2173_);
v___x_2175_ = v___x_2162_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
size_t v___x_2181_; size_t v___x_2182_; uint8_t v___x_2183_; 
v___x_2181_ = lean_ptr_addr(v_decl_2164_);
v___x_2182_ = lean_ptr_addr(v_a_2160_);
v___x_2183_ = lean_usize_dec_eq(v___x_2181_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2193_; 
v_isSharedCheck_2193_ = !lean_is_exclusive(v_code_1961_);
if (v_isSharedCheck_2193_ == 0)
{
lean_object* v_unused_2194_; lean_object* v_unused_2195_; 
v_unused_2194_ = lean_ctor_get(v_code_1961_, 1);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v_code_1961_, 0);
lean_dec(v_unused_2195_);
v___x_2185_ = v_code_1961_;
v_isShared_2186_ = v_isSharedCheck_2193_;
goto v_resetjp_2184_;
}
else
{
lean_dec(v_code_1961_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2193_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 1, v_a_1999_);
lean_ctor_set(v___x_2185_, 0, v_a_2160_);
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2160_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_a_1999_);
v___x_2188_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
lean_object* v___x_2190_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2188_);
v___x_2190_ = v___x_2162_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_object* v___x_2197_; 
lean_dec(v_a_2160_);
lean_dec(v_a_1999_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v_code_1961_);
v___x_2197_ = v___x_2162_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_code_1961_);
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
}
else
{
lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; 
v_unused_2209_ = lean_ctor_get(v___x_2159_, 0);
lean_dec(v_unused_2209_);
v___x_2201_ = v___x_2159_;
v_isShared_2202_ = v_isSharedCheck_2208_;
goto v_resetjp_2200_;
}
else
{
lean_dec(v___x_2159_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2208_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2203_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2204_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2203_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2204_);
v___x_2206_ = v___x_2201_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v_a_2210_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2159_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2159_);
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
}
}
v___jp_2101_:
{
lean_object* v___x_2102_; 
v___x_2102_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2100_, v___f_1992_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v_fst_2104_; lean_object* v_snd_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v_fst_2104_ = lean_ctor_get(v_a_2103_, 0);
lean_inc(v_fst_2104_);
v_snd_2105_ = lean_ctor_get(v_a_2103_, 1);
lean_inc(v_snd_2105_);
lean_dec(v_a_2103_);
lean_inc_ref(v_value_2003_);
v___x_2106_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_value_2003_, v_fst_2104_);
v___x_2107_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1995_, v_a_1997_, v___x_2106_, v_a_1967_);
if (lean_obj_tag(v___x_2107_) == 0)
{
if (lean_obj_tag(v_code_1961_) == 0)
{
lean_object* v_a_2108_; lean_object* v_decl_2109_; lean_object* v_k_2110_; size_t v___x_2111_; size_t v___x_2112_; uint8_t v___x_2113_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v_decl_2109_ = lean_ctor_get(v_code_1961_, 0);
v_k_2110_ = lean_ctor_get(v_code_1961_, 1);
v___x_2111_ = lean_ptr_addr(v_k_2110_);
v___x_2112_ = lean_ptr_addr(v_a_1999_);
v___x_2113_ = lean_usize_dec_eq(v___x_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
v_isSharedCheck_2120_ = !lean_is_exclusive(v_code_1961_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; lean_object* v_unused_2122_; 
v_unused_2121_ = lean_ctor_get(v_code_1961_, 1);
lean_dec(v_unused_2121_);
v_unused_2122_ = lean_ctor_get(v_code_1961_, 0);
lean_dec(v_unused_2122_);
v___x_2115_ = v_code_1961_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_dec(v_code_1961_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 1, v_a_1999_);
lean_ctor_set(v___x_2115_, 0, v_a_2108_);
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2108_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_a_1999_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
v___y_1977_ = v_snd_2105_;
v___y_1978_ = v___x_2118_;
goto v___jp_1976_;
}
}
}
else
{
size_t v___x_2123_; size_t v___x_2124_; uint8_t v___x_2125_; 
v___x_2123_ = lean_ptr_addr(v_decl_2109_);
v___x_2124_ = lean_ptr_addr(v_a_2108_);
v___x_2125_ = lean_usize_dec_eq(v___x_2123_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
v_isSharedCheck_2132_ = !lean_is_exclusive(v_code_1961_);
if (v_isSharedCheck_2132_ == 0)
{
lean_object* v_unused_2133_; lean_object* v_unused_2134_; 
v_unused_2133_ = lean_ctor_get(v_code_1961_, 1);
lean_dec(v_unused_2133_);
v_unused_2134_ = lean_ctor_get(v_code_1961_, 0);
lean_dec(v_unused_2134_);
v___x_2127_ = v_code_1961_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_dec(v_code_1961_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 1, v_a_1999_);
lean_ctor_set(v___x_2127_, 0, v_a_2108_);
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2108_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_a_1999_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
v___y_1977_ = v_snd_2105_;
v___y_1978_ = v___x_2130_;
goto v___jp_1976_;
}
}
}
else
{
lean_dec(v_a_2108_);
lean_dec(v_a_1999_);
v___y_1977_ = v_snd_2105_;
v___y_1978_ = v_code_1961_;
goto v___jp_1976_;
}
}
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec_ref_known(v___x_2107_, 1);
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v___x_2135_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2136_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2135_);
v___y_1977_ = v_snd_2105_;
v___y_1978_ = v___x_2136_;
goto v___jp_1976_;
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_snd_2105_);
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v_a_2137_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2107_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2107_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec_ref(v_code_1961_);
v_a_2145_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2102_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2102_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
case 6:
{
lean_inc_ref(v_value_2003_);
lean_del_object(v___x_2001_);
v___y_2005_ = v_a_1967_;
goto v___jp_2004_;
}
case 7:
{
lean_inc_ref(v_value_2003_);
lean_del_object(v___x_2001_);
v___y_2005_ = v_a_1967_;
goto v___jp_2004_;
}
case 9:
{
lean_object* v_fn_2219_; lean_object* v_args_2220_; lean_object* v___x_2221_; 
lean_del_object(v___x_2001_);
lean_dec(v_a_1994_);
v_fn_2219_ = lean_ctor_get(v_value_2003_, 0);
v_args_2220_ = lean_ctor_get(v_value_2003_, 1);
lean_inc(v_fn_2219_);
v___x_2221_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_2219_, v_a_1969_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
if (lean_obj_tag(v_a_2222_) == 1)
{
lean_object* v_val_2223_; lean_object* v_type_2224_; lean_object* v_params_2225_; lean_object* v___f_2226_; lean_object* v___x_2227_; 
v_val_2223_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_val_2223_);
lean_dec_ref_known(v_a_2222_, 1);
v_type_2224_ = lean_ctor_get(v_val_2223_, 2);
lean_inc_ref(v_type_2224_);
v_params_2225_ = lean_ctor_get(v_val_2223_, 3);
lean_inc_ref(v_params_2225_);
lean_dec(v_val_2223_);
v___f_2226_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4___boxed), 2, 1);
lean_closure_set(v___f_2226_, 0, v_params_2225_);
v___x_2227_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2220_, v___f_2226_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v_fst_2229_; lean_object* v_snd_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2227_, 1);
v_fst_2229_ = lean_ctor_get(v_a_2228_, 0);
lean_inc(v_fst_2229_);
v_snd_2230_ = lean_ctor_get(v_a_2228_, 1);
lean_inc(v_snd_2230_);
lean_dec(v_a_2228_);
lean_inc_ref(v_value_2003_);
v___x_2231_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_value_2003_, v_fst_2229_);
v___x_2232_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1995_, v_a_1997_, v___x_2231_, v_a_1967_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2234_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v___x_2234_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(v_code_1961_, v_a_2233_, v_type_2224_, v_a_1999_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
lean_dec_ref(v_type_2224_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2243_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2243_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2243_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2239_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_2230_, v_a_2235_);
lean_dec(v_snd_2230_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2239_);
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
else
{
lean_dec(v_snd_2230_);
return v___x_2234_;
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec(v_snd_2230_);
lean_dec_ref(v_type_2224_);
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v_a_2244_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2232_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2232_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec_ref(v_type_2224_);
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec_ref(v_code_1961_);
v_a_2252_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2227_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2227_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec(v_a_2222_);
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec_ref(v_code_1961_);
v___x_2260_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3);
v___x_2261_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2260_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
return v___x_2261_;
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec_ref(v_code_1961_);
v_a_2262_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2221_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2221_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
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
case 10:
{
lean_object* v_fn_2270_; lean_object* v_args_2271_; lean_object* v___x_2272_; 
lean_del_object(v___x_2001_);
lean_dec(v_a_1994_);
v_fn_2270_ = lean_ctor_get(v_value_2003_, 0);
v_args_2271_ = lean_ctor_get(v_value_2003_, 1);
lean_inc(v_fn_2270_);
v___x_2272_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_2270_, v_a_1969_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
if (lean_obj_tag(v_a_2273_) == 1)
{
lean_object* v_val_2274_; lean_object* v___x_2275_; 
v_val_2274_ = lean_ctor_get(v_a_2273_, 0);
lean_inc(v_val_2274_);
lean_dec_ref_known(v_a_2273_, 1);
v___x_2275_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_val_2274_, v_a_1969_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___y_2278_; uint8_t v___x_2330_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
v___x_2330_ = lean_unbox(v_a_2276_);
lean_dec(v_a_2276_);
if (v___x_2330_ == 0)
{
lean_inc(v_fn_2270_);
v___y_2278_ = v_fn_2270_;
goto v___jp_2277_;
}
else
{
lean_object* v___x_2331_; 
lean_inc(v_fn_2270_);
v___x_2331_ = l_Lean_Compiler_LCNF_mkBoxedName(v_fn_2270_);
v___y_2278_ = v___x_2331_;
goto v___jp_2277_;
}
v___jp_2277_:
{
lean_object* v___x_2279_; 
v___x_2279_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2271_, v___f_1992_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v_fst_2281_; lean_object* v_snd_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v_fst_2281_ = lean_ctor_get(v_a_2280_, 0);
lean_inc(v_fst_2281_);
v_snd_2282_ = lean_ctor_get(v_a_2280_, 1);
lean_inc(v_snd_2282_);
lean_dec(v_a_2280_);
lean_inc_ref(v_value_2003_);
v___x_2283_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updatePapImp___redArg(v_value_2003_, v___y_2278_, v_fst_2281_);
v___x_2284_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1995_, v_a_1997_, v___x_2283_, v_a_1967_);
if (lean_obj_tag(v___x_2284_) == 0)
{
if (lean_obj_tag(v_code_1961_) == 0)
{
lean_object* v_a_2285_; lean_object* v_decl_2286_; lean_object* v_k_2287_; size_t v___x_2288_; size_t v___x_2289_; uint8_t v___x_2290_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v_decl_2286_ = lean_ctor_get(v_code_1961_, 0);
v_k_2287_ = lean_ctor_get(v_code_1961_, 1);
v___x_2288_ = lean_ptr_addr(v_k_2287_);
v___x_2289_ = lean_ptr_addr(v_a_1999_);
v___x_2290_ = lean_usize_dec_eq(v___x_2288_, v___x_2289_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
v_isSharedCheck_2297_ = !lean_is_exclusive(v_code_1961_);
if (v_isSharedCheck_2297_ == 0)
{
lean_object* v_unused_2298_; lean_object* v_unused_2299_; 
v_unused_2298_ = lean_ctor_get(v_code_1961_, 1);
lean_dec(v_unused_2298_);
v_unused_2299_ = lean_ctor_get(v_code_1961_, 0);
lean_dec(v_unused_2299_);
v___x_2292_ = v_code_1961_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_dec(v_code_1961_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 1, v_a_1999_);
lean_ctor_set(v___x_2292_, 0, v_a_2285_);
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2285_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_a_1999_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
v___y_1972_ = v_snd_2282_;
v___y_1973_ = v___x_2295_;
goto v___jp_1971_;
}
}
}
else
{
size_t v___x_2300_; size_t v___x_2301_; uint8_t v___x_2302_; 
v___x_2300_ = lean_ptr_addr(v_decl_2286_);
v___x_2301_ = lean_ptr_addr(v_a_2285_);
v___x_2302_ = lean_usize_dec_eq(v___x_2300_, v___x_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
v_isSharedCheck_2309_ = !lean_is_exclusive(v_code_1961_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; lean_object* v_unused_2311_; 
v_unused_2310_ = lean_ctor_get(v_code_1961_, 1);
lean_dec(v_unused_2310_);
v_unused_2311_ = lean_ctor_get(v_code_1961_, 0);
lean_dec(v_unused_2311_);
v___x_2304_ = v_code_1961_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_dec(v_code_1961_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 1, v_a_1999_);
lean_ctor_set(v___x_2304_, 0, v_a_2285_);
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2285_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_a_1999_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
v___y_1972_ = v_snd_2282_;
v___y_1973_ = v___x_2307_;
goto v___jp_1971_;
}
}
}
else
{
lean_dec(v_a_2285_);
lean_dec(v_a_1999_);
v___y_1972_ = v_snd_2282_;
v___y_1973_ = v_code_1961_;
goto v___jp_1971_;
}
}
}
else
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
lean_dec_ref_known(v___x_2284_, 1);
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v___x_2312_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2313_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2312_);
v___y_1972_ = v_snd_2282_;
v___y_1973_ = v___x_2313_;
goto v___jp_1971_;
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v_snd_2282_);
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v_a_2314_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2284_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2284_);
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
lean_dec(v___y_2278_);
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec_ref(v_code_1961_);
v_a_2322_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2279_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2279_);
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
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec_ref(v_code_1961_);
v_a_2332_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2275_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2275_);
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
lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec(v_a_2273_);
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec_ref(v_code_1961_);
v___x_2340_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4);
v___x_2341_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2340_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
return v___x_2341_;
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec_ref(v_code_1961_);
v_a_2342_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2272_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2272_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
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
case 11:
{
lean_inc_ref(v_value_2003_);
lean_del_object(v___x_2001_);
v___y_2005_ = v_a_1967_;
goto v___jp_2004_;
}
case 12:
{
lean_object* v_args_2350_; lean_object* v___x_2351_; 
lean_del_object(v___x_2001_);
lean_dec(v_a_1994_);
v_args_2350_ = lean_ctor_get(v_value_2003_, 2);
v___x_2351_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2350_, v___f_1992_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v_fst_2353_; lean_object* v_snd_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v_fst_2353_ = lean_ctor_get(v_a_2352_, 0);
lean_inc(v_fst_2353_);
v_snd_2354_ = lean_ctor_get(v_a_2352_, 1);
lean_inc(v_snd_2354_);
lean_dec(v_a_2352_);
lean_inc_ref(v_value_2003_);
v___x_2355_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_value_2003_, v_fst_2353_);
v___x_2356_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1995_, v_a_1997_, v___x_2355_, v_a_1967_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2395_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2395_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2395_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___y_2362_; 
if (lean_obj_tag(v_code_1961_) == 0)
{
lean_object* v_decl_2367_; lean_object* v_k_2368_; size_t v___x_2369_; size_t v___x_2370_; uint8_t v___x_2371_; 
v_decl_2367_ = lean_ctor_get(v_code_1961_, 0);
v_k_2368_ = lean_ctor_get(v_code_1961_, 1);
v___x_2369_ = lean_ptr_addr(v_k_2368_);
v___x_2370_ = lean_ptr_addr(v_a_1999_);
v___x_2371_ = lean_usize_dec_eq(v___x_2369_, v___x_2370_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
v_isSharedCheck_2378_ = !lean_is_exclusive(v_code_1961_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; lean_object* v_unused_2380_; 
v_unused_2379_ = lean_ctor_get(v_code_1961_, 1);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v_code_1961_, 0);
lean_dec(v_unused_2380_);
v___x_2373_ = v_code_1961_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_dec(v_code_1961_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 1, v_a_1999_);
lean_ctor_set(v___x_2373_, 0, v_a_2357_);
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2357_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_a_1999_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
v___y_2362_ = v___x_2376_;
goto v___jp_2361_;
}
}
}
else
{
size_t v___x_2381_; size_t v___x_2382_; uint8_t v___x_2383_; 
v___x_2381_ = lean_ptr_addr(v_decl_2367_);
v___x_2382_ = lean_ptr_addr(v_a_2357_);
v___x_2383_ = lean_usize_dec_eq(v___x_2381_, v___x_2382_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
v_isSharedCheck_2390_ = !lean_is_exclusive(v_code_1961_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; lean_object* v_unused_2392_; 
v_unused_2391_ = lean_ctor_get(v_code_1961_, 1);
lean_dec(v_unused_2391_);
v_unused_2392_ = lean_ctor_get(v_code_1961_, 0);
lean_dec(v_unused_2392_);
v___x_2385_ = v_code_1961_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_dec(v_code_1961_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 1, v_a_1999_);
lean_ctor_set(v___x_2385_, 0, v_a_2357_);
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2357_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_a_1999_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
v___y_2362_ = v___x_2388_;
goto v___jp_2361_;
}
}
}
else
{
lean_dec(v_a_2357_);
lean_dec(v_a_1999_);
v___y_2362_ = v_code_1961_;
goto v___jp_2361_;
}
}
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec(v_a_2357_);
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v___x_2393_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2394_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2393_);
v___y_2362_ = v___x_2394_;
goto v___jp_2361_;
}
v___jp_2361_:
{
lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2363_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_2354_, v___y_2362_);
lean_dec(v_snd_2354_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2363_);
v___x_2365_ = v___x_2359_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_snd_2354_);
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v_a_2396_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2356_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2356_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec_ref(v_code_1961_);
v_a_2404_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2351_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2351_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
case 13:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_del_object(v___x_2001_);
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec(v_a_1994_);
lean_dec_ref(v_code_1961_);
v___x_2412_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1);
v___x_2413_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2412_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
return v___x_2413_;
}
case 14:
{
lean_del_object(v___x_2001_);
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec(v_a_1994_);
lean_dec_ref(v_code_1961_);
v___y_1982_ = v_a_1964_;
v___y_1983_ = v_a_1965_;
v___y_1984_ = v_a_1966_;
v___y_1985_ = v_a_1967_;
v___y_1986_ = v_a_1968_;
v___y_1987_ = v_a_1969_;
goto v___jp_1981_;
}
case 15:
{
lean_del_object(v___x_2001_);
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec(v_a_1994_);
lean_dec_ref(v_code_1961_);
v___y_1982_ = v_a_1964_;
v___y_1983_ = v_a_1965_;
v___y_1984_ = v_a_1966_;
v___y_1985_ = v_a_1967_;
v___y_1986_ = v_a_1968_;
v___y_1987_ = v_a_1969_;
goto v___jp_1981_;
}
default: 
{
lean_object* v___x_2414_; 
lean_inc(v_value_2003_);
lean_del_object(v___x_2001_);
v___x_2414_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_1995_, v_a_1997_, v_a_1994_, v_value_2003_, v_a_1967_);
if (lean_obj_tag(v___x_2414_) == 0)
{
if (lean_obj_tag(v_code_1961_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2454_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2417_ = v___x_2414_;
v_isShared_2418_ = v_isSharedCheck_2454_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2454_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v_decl_2419_; lean_object* v_k_2420_; size_t v___x_2421_; size_t v___x_2422_; uint8_t v___x_2423_; 
v_decl_2419_ = lean_ctor_get(v_code_1961_, 0);
v_k_2420_ = lean_ctor_get(v_code_1961_, 1);
v___x_2421_ = lean_ptr_addr(v_k_2420_);
v___x_2422_ = lean_ptr_addr(v_a_1999_);
v___x_2423_ = lean_usize_dec_eq(v___x_2421_, v___x_2422_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2433_; 
v_isSharedCheck_2433_ = !lean_is_exclusive(v_code_1961_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; lean_object* v_unused_2435_; 
v_unused_2434_ = lean_ctor_get(v_code_1961_, 1);
lean_dec(v_unused_2434_);
v_unused_2435_ = lean_ctor_get(v_code_1961_, 0);
lean_dec(v_unused_2435_);
v___x_2425_ = v_code_1961_;
v_isShared_2426_ = v_isSharedCheck_2433_;
goto v_resetjp_2424_;
}
else
{
lean_dec(v_code_1961_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2433_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 1, v_a_1999_);
lean_ctor_set(v___x_2425_, 0, v_a_2415_);
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2415_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_a_1999_);
v___x_2428_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
lean_object* v___x_2430_; 
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v___x_2428_);
v___x_2430_ = v___x_2417_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
size_t v___x_2436_; size_t v___x_2437_; uint8_t v___x_2438_; 
v___x_2436_ = lean_ptr_addr(v_decl_2419_);
v___x_2437_ = lean_ptr_addr(v_a_2415_);
v___x_2438_ = lean_usize_dec_eq(v___x_2436_, v___x_2437_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2448_; 
v_isSharedCheck_2448_ = !lean_is_exclusive(v_code_1961_);
if (v_isSharedCheck_2448_ == 0)
{
lean_object* v_unused_2449_; lean_object* v_unused_2450_; 
v_unused_2449_ = lean_ctor_get(v_code_1961_, 1);
lean_dec(v_unused_2449_);
v_unused_2450_ = lean_ctor_get(v_code_1961_, 0);
lean_dec(v_unused_2450_);
v___x_2440_ = v_code_1961_;
v_isShared_2441_ = v_isSharedCheck_2448_;
goto v_resetjp_2439_;
}
else
{
lean_dec(v_code_1961_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2448_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 1, v_a_1999_);
lean_ctor_set(v___x_2440_, 0, v_a_2415_);
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2415_);
lean_ctor_set(v_reuseFailAlloc_2447_, 1, v_a_1999_);
v___x_2443_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2445_; 
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v___x_2443_);
v___x_2445_ = v___x_2417_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
else
{
lean_object* v___x_2452_; 
lean_dec(v_a_2415_);
lean_dec(v_a_1999_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v_code_1961_);
v___x_2452_ = v___x_2417_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_code_1961_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
else
{
lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; 
v_unused_2464_ = lean_ctor_get(v___x_2414_, 0);
lean_dec(v_unused_2464_);
v___x_2456_ = v___x_2414_;
v_isShared_2457_ = v_isSharedCheck_2463_;
goto v_resetjp_2455_;
}
else
{
lean_dec(v___x_2414_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2463_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2458_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2459_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2458_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2459_);
v___x_2461_ = v___x_2456_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v_a_2465_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2414_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2414_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
v___jp_2004_:
{
lean_object* v___x_2006_; 
v___x_2006_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_1995_, v_a_1997_, v_a_1994_, v_value_2003_, v___y_2005_);
if (lean_obj_tag(v___x_2006_) == 0)
{
if (lean_obj_tag(v_code_1961_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2046_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2046_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2046_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_decl_2011_; lean_object* v_k_2012_; size_t v___x_2013_; size_t v___x_2014_; uint8_t v___x_2015_; 
v_decl_2011_ = lean_ctor_get(v_code_1961_, 0);
v_k_2012_ = lean_ctor_get(v_code_1961_, 1);
v___x_2013_ = lean_ptr_addr(v_k_2012_);
v___x_2014_ = lean_ptr_addr(v_a_1999_);
v___x_2015_ = lean_usize_dec_eq(v___x_2013_, v___x_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2025_; 
v_isSharedCheck_2025_ = !lean_is_exclusive(v_code_1961_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; lean_object* v_unused_2027_; 
v_unused_2026_ = lean_ctor_get(v_code_1961_, 1);
lean_dec(v_unused_2026_);
v_unused_2027_ = lean_ctor_get(v_code_1961_, 0);
lean_dec(v_unused_2027_);
v___x_2017_ = v_code_1961_;
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v_code_1961_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 1, v_a_1999_);
lean_ctor_set(v___x_2017_, 0, v_a_2007_);
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2007_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_a_1999_);
v___x_2020_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2022_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2020_);
v___x_2022_ = v___x_2009_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
else
{
size_t v___x_2028_; size_t v___x_2029_; uint8_t v___x_2030_; 
v___x_2028_ = lean_ptr_addr(v_decl_2011_);
v___x_2029_ = lean_ptr_addr(v_a_2007_);
v___x_2030_ = lean_usize_dec_eq(v___x_2028_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2040_; 
v_isSharedCheck_2040_ = !lean_is_exclusive(v_code_1961_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; lean_object* v_unused_2042_; 
v_unused_2041_ = lean_ctor_get(v_code_1961_, 1);
lean_dec(v_unused_2041_);
v_unused_2042_ = lean_ctor_get(v_code_1961_, 0);
lean_dec(v_unused_2042_);
v___x_2032_ = v_code_1961_;
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
else
{
lean_dec(v_code_1961_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v_a_1999_);
lean_ctor_set(v___x_2032_, 0, v_a_2007_);
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2007_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_a_1999_);
v___x_2035_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2035_);
v___x_2037_ = v___x_2009_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v___x_2044_; 
lean_dec(v_a_2007_);
lean_dec(v_a_1999_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v_code_1961_);
v___x_2044_ = v___x_2009_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_code_1961_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
else
{
lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; 
v_unused_2056_ = lean_ctor_get(v___x_2006_, 0);
lean_dec(v_unused_2056_);
v___x_2048_ = v___x_2006_;
v_isShared_2049_ = v_isSharedCheck_2055_;
goto v_resetjp_2047_;
}
else
{
lean_dec(v___x_2006_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2055_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2050_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2051_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2050_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2051_);
v___x_2053_ = v___x_2048_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1961_);
v_a_2057_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2006_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2006_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1997_);
lean_dec(v_a_1994_);
lean_dec_ref(v_code_1961_);
return v___x_1998_;
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v_a_1994_);
lean_dec_ref(v_k_1963_);
lean_dec_ref(v_code_1961_);
v_a_2474_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_1996_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_1996_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec(v_value_1991_);
lean_dec_ref(v_k_1963_);
lean_dec_ref(v_decl_1962_);
lean_dec_ref(v_code_1961_);
v_a_2482_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_1993_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_1993_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
v___jp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___y_1972_, v___y_1973_);
lean_dec_ref(v___y_1972_);
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
return v___x_1975_;
}
v___jp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___y_1977_, v___y_1978_);
lean_dec_ref(v___y_1977_);
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
return v___x_1980_;
}
v___jp_1981_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1);
v___x_1989_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_1988_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
return v___x_1989_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2491_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_2492_ = lean_unsigned_to_nat(44u);
v___x_2493_ = lean_unsigned_to_nat(284u);
v___x_2494_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0));
v___x_2495_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_2496_ = l_mkPanicMessageWithDecl(v___x_2495_, v___x_2494_, v___x_2493_, v___x_2492_, v___x_2491_);
return v___x_2496_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2497_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_2498_ = lean_unsigned_to_nat(59u);
v___x_2499_ = lean_unsigned_to_nat(287u);
v___x_2500_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0));
v___x_2501_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_2502_ = l_mkPanicMessageWithDecl(v___x_2501_, v___x_2500_, v___x_2499_, v___x_2498_, v___x_2497_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(lean_object* v_code_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
switch(lean_obj_tag(v_code_2503_))
{
case 0:
{
lean_object* v_decl_2511_; lean_object* v_k_2512_; lean_object* v___x_2513_; 
v_decl_2511_ = lean_ctor_get(v_code_2503_, 0);
lean_inc_ref(v_decl_2511_);
v_k_2512_ = lean_ctor_get(v_code_2503_, 1);
lean_inc_ref(v_k_2512_);
v___x_2513_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(v_code_2503_, v_decl_2511_, v_k_2512_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
return v___x_2513_;
}
case 2:
{
lean_object* v_decl_2514_; lean_object* v_k_2515_; lean_object* v_params_2516_; lean_object* v_value_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; 
v_decl_2514_ = lean_ctor_get(v_code_2503_, 0);
v_k_2515_ = lean_ctor_get(v_code_2503_, 1);
v_params_2516_ = lean_ctor_get(v_decl_2514_, 2);
v_value_2517_ = lean_ctor_get(v_decl_2514_, 4);
v___x_2518_ = 1;
lean_inc_ref(v_value_2517_);
v___x_2519_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_value_2517_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v_currDeclResultType_2521_; lean_object* v___x_2522_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v_currDeclResultType_2521_ = lean_ctor_get(v_a_2504_, 1);
lean_inc_ref(v_params_2516_);
lean_inc_ref(v_currDeclResultType_2521_);
lean_inc_ref(v_decl_2514_);
v___x_2522_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2518_, v_decl_2514_, v_currDeclResultType_2521_, v_params_2516_, v_a_2520_, v_a_2507_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2524_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v___x_2522_, 1);
lean_inc_ref(v_k_2515_);
v___x_2524_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2515_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2562_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2562_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2562_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
size_t v___x_2529_; size_t v___x_2530_; uint8_t v___x_2531_; 
v___x_2529_ = lean_ptr_addr(v_k_2515_);
v___x_2530_ = lean_ptr_addr(v_a_2525_);
v___x_2531_ = lean_usize_dec_eq(v___x_2529_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2541_; 
v_isSharedCheck_2541_ = !lean_is_exclusive(v_code_2503_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; lean_object* v_unused_2543_; 
v_unused_2542_ = lean_ctor_get(v_code_2503_, 1);
lean_dec(v_unused_2542_);
v_unused_2543_ = lean_ctor_get(v_code_2503_, 0);
lean_dec(v_unused_2543_);
v___x_2533_ = v_code_2503_;
v_isShared_2534_ = v_isSharedCheck_2541_;
goto v_resetjp_2532_;
}
else
{
lean_dec(v_code_2503_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2541_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v_a_2525_);
lean_ctor_set(v___x_2533_, 0, v_a_2523_);
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2523_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_a_2525_);
v___x_2536_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2538_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2536_);
v___x_2538_ = v___x_2527_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
else
{
size_t v___x_2544_; size_t v___x_2545_; uint8_t v___x_2546_; 
v___x_2544_ = lean_ptr_addr(v_decl_2514_);
v___x_2545_ = lean_ptr_addr(v_a_2523_);
v___x_2546_ = lean_usize_dec_eq(v___x_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2556_; 
v_isSharedCheck_2556_ = !lean_is_exclusive(v_code_2503_);
if (v_isSharedCheck_2556_ == 0)
{
lean_object* v_unused_2557_; lean_object* v_unused_2558_; 
v_unused_2557_ = lean_ctor_get(v_code_2503_, 1);
lean_dec(v_unused_2557_);
v_unused_2558_ = lean_ctor_get(v_code_2503_, 0);
lean_dec(v_unused_2558_);
v___x_2548_ = v_code_2503_;
v_isShared_2549_ = v_isSharedCheck_2556_;
goto v_resetjp_2547_;
}
else
{
lean_dec(v_code_2503_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2556_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 1, v_a_2525_);
lean_ctor_set(v___x_2548_, 0, v_a_2523_);
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2523_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_a_2525_);
v___x_2551_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2553_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2551_);
v___x_2553_ = v___x_2527_;
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
lean_object* v___x_2560_; 
lean_dec(v_a_2525_);
lean_dec(v_a_2523_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v_code_2503_);
v___x_2560_ = v___x_2527_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_code_2503_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
else
{
lean_dec(v_a_2523_);
lean_dec_ref_known(v_code_2503_, 2);
return v___x_2524_;
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref_known(v_code_2503_, 2);
v_a_2563_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2522_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2522_);
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
lean_dec_ref_known(v_code_2503_, 2);
return v___x_2519_;
}
}
case 3:
{
lean_object* v_fvarId_2571_; lean_object* v_args_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; 
v_fvarId_2571_ = lean_ctor_get(v_code_2503_, 0);
v_args_2572_ = lean_ctor_get(v_code_2503_, 1);
v___x_2573_ = 1;
v___x_2574_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_2573_, v_fvarId_2571_, v_a_2507_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2574_, 1);
if (lean_obj_tag(v_a_2575_) == 1)
{
lean_object* v_val_2576_; lean_object* v_params_2577_; lean_object* v___f_2578_; lean_object* v___x_2579_; 
v_val_2576_ = lean_ctor_get(v_a_2575_, 0);
lean_inc(v_val_2576_);
lean_dec_ref_known(v_a_2575_, 1);
v_params_2577_ = lean_ctor_get(v_val_2576_, 2);
lean_inc_ref(v_params_2577_);
lean_dec(v_val_2576_);
v___f_2578_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2578_, 0, v_params_2577_);
v___x_2579_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2572_, v___f_2578_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2614_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2614_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2614_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v_fst_2584_; lean_object* v_snd_2585_; lean_object* v___y_2587_; uint8_t v___x_2592_; 
v_fst_2584_ = lean_ctor_get(v_a_2580_, 0);
lean_inc(v_fst_2584_);
v_snd_2585_ = lean_ctor_get(v_a_2580_, 1);
lean_inc(v_snd_2585_);
lean_dec(v_a_2580_);
v___x_2592_ = l_Lean_instBEqFVarId_beq(v_fvarId_2571_, v_fvarId_2571_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_inc(v_fvarId_2571_);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_code_2503_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; lean_object* v_unused_2601_; 
v_unused_2600_ = lean_ctor_get(v_code_2503_, 1);
lean_dec(v_unused_2600_);
v_unused_2601_ = lean_ctor_get(v_code_2503_, 0);
lean_dec(v_unused_2601_);
v___x_2594_ = v_code_2503_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_dec(v_code_2503_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 1, v_fst_2584_);
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_fvarId_2571_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_fst_2584_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
v___y_2587_ = v___x_2597_;
goto v___jp_2586_;
}
}
}
else
{
size_t v___x_2602_; size_t v___x_2603_; uint8_t v___x_2604_; 
v___x_2602_ = lean_ptr_addr(v_args_2572_);
v___x_2603_ = lean_ptr_addr(v_fst_2584_);
v___x_2604_ = lean_usize_dec_eq(v___x_2602_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_inc(v_fvarId_2571_);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_code_2503_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; lean_object* v_unused_2613_; 
v_unused_2612_ = lean_ctor_get(v_code_2503_, 1);
lean_dec(v_unused_2612_);
v_unused_2613_ = lean_ctor_get(v_code_2503_, 0);
lean_dec(v_unused_2613_);
v___x_2606_ = v_code_2503_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_dec(v_code_2503_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 1, v_fst_2584_);
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_fvarId_2571_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_fst_2584_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
v___y_2587_ = v___x_2609_;
goto v___jp_2586_;
}
}
}
else
{
lean_dec(v_fst_2584_);
v___y_2587_ = v_code_2503_;
goto v___jp_2586_;
}
}
v___jp_2586_:
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2588_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_2585_, v___y_2587_);
lean_dec(v_snd_2585_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v___x_2588_);
v___x_2590_ = v___x_2582_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref_known(v_code_2503_, 2);
v_a_2615_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2579_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2579_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec(v_a_2575_);
lean_dec_ref_known(v_code_2503_, 2);
v___x_2623_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1);
v___x_2624_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2623_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
return v___x_2624_;
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref_known(v_code_2503_, 2);
v_a_2625_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2574_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2574_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
case 4:
{
lean_object* v_cases_2633_; lean_object* v_typeName_2634_; lean_object* v_resultType_2635_; lean_object* v_discr_2636_; lean_object* v_alts_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_cases_2633_ = lean_ctor_get(v_code_2503_, 0);
v_typeName_2634_ = lean_ctor_get(v_cases_2633_, 0);
lean_inc(v_typeName_2634_);
v_resultType_2635_ = lean_ctor_get(v_cases_2633_, 1);
lean_inc_ref(v_resultType_2635_);
v_discr_2636_ = lean_ctor_get(v_cases_2633_, 2);
lean_inc(v_discr_2636_);
v_alts_2637_ = lean_ctor_get(v_cases_2633_, 3);
lean_inc_ref_n(v_alts_2637_, 2);
v___x_2638_ = 1;
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(v___x_2639_, v_alts_2637_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2640_, 1);
v___x_2642_ = lean_box(0);
lean_inc(v_typeName_2634_);
v___x_2643_ = l_Lean_mkConst(v_typeName_2634_, v___x_2642_);
lean_inc(v_discr_2636_);
v___x_2644_ = l_Lean_Compiler_LCNF_getType(v_discr_2636_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; uint8_t v___x_2646_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
v___x_2646_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2645_, v___x_2643_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; 
lean_inc_ref(v___x_2643_);
lean_inc(v_discr_2636_);
v___x_2647_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_discr_2636_, v_a_2645_, v___x_2643_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v___x_2649_ = lean_box(0);
v___x_2650_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2638_, v___x_2649_, v___x_2643_, v_a_2648_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v_fvarId_2652_; lean_object* v___x_2653_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v_fvarId_2652_ = lean_ctor_get(v_a_2651_, 0);
lean_inc(v_fvarId_2652_);
v___x_2653_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_2634_, v_a_2641_, v_alts_2637_, v_resultType_2635_, v_discr_2636_, v_code_2503_, v_fvarId_2652_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec(v_discr_2636_);
lean_dec_ref(v_resultType_2635_);
lean_dec_ref(v_alts_2637_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2662_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2656_ = v___x_2653_;
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v_a_2651_);
lean_ctor_set(v___x_2658_, 1, v_a_2654_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2658_);
v___x_2660_ = v___x_2656_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
else
{
lean_dec(v_a_2651_);
return v___x_2653_;
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec(v_a_2641_);
lean_dec_ref(v_alts_2637_);
lean_dec(v_discr_2636_);
lean_dec_ref(v_resultType_2635_);
lean_dec(v_typeName_2634_);
lean_dec_ref_known(v_code_2503_, 1);
v_a_2663_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2650_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2650_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec_ref(v___x_2643_);
lean_dec(v_a_2641_);
lean_dec_ref(v_alts_2637_);
lean_dec(v_discr_2636_);
lean_dec_ref(v_resultType_2635_);
lean_dec(v_typeName_2634_);
lean_dec_ref_known(v_code_2503_, 1);
v_a_2671_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2647_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2647_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
else
{
lean_object* v___x_2679_; 
lean_dec(v_a_2645_);
lean_dec_ref(v___x_2643_);
lean_inc(v_discr_2636_);
v___x_2679_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_2634_, v_a_2641_, v_alts_2637_, v_resultType_2635_, v_discr_2636_, v_code_2503_, v_discr_2636_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec(v_discr_2636_);
lean_dec_ref(v_resultType_2635_);
lean_dec_ref(v_alts_2637_);
return v___x_2679_;
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec_ref(v___x_2643_);
lean_dec(v_a_2641_);
lean_dec_ref(v_alts_2637_);
lean_dec(v_discr_2636_);
lean_dec_ref(v_resultType_2635_);
lean_dec(v_typeName_2634_);
lean_dec_ref_known(v_code_2503_, 1);
v_a_2680_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2644_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2644_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec_ref(v_alts_2637_);
lean_dec(v_discr_2636_);
lean_dec_ref(v_resultType_2635_);
lean_dec(v_typeName_2634_);
lean_dec_ref_known(v_code_2503_, 1);
v_a_2688_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2640_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2640_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_2696_; lean_object* v_currDeclResultType_2697_; lean_object* v___x_2698_; 
v_fvarId_2696_ = lean_ctor_get(v_code_2503_, 0);
lean_inc_n(v_fvarId_2696_, 2);
v_currDeclResultType_2697_ = lean_ctor_get(v_a_2504_, 1);
v___x_2698_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2696_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; uint8_t v___x_2700_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2699_, v_currDeclResultType_2697_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; 
lean_inc_ref(v_currDeclResultType_2697_);
lean_inc(v_fvarId_2696_);
v___x_2701_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_2696_, v_a_2699_, v_currDeclResultType_2697_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; uint8_t v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = 1;
v___x_2704_ = lean_box(0);
lean_inc_ref(v_currDeclResultType_2697_);
v___x_2705_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2703_, v___x_2704_, v_currDeclResultType_2697_, v_a_2702_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v_fvarId_2707_; lean_object* v___x_2708_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v_fvarId_2707_ = lean_ctor_get(v_a_2706_, 0);
lean_inc(v_fvarId_2707_);
v___x_2708_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_2696_, v_code_2503_, v_fvarId_2707_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec(v_fvarId_2696_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2717_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2711_ = v___x_2708_;
v_isShared_2712_ = v_isSharedCheck_2717_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2708_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2717_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2713_, 0, v_a_2706_);
lean_ctor_set(v___x_2713_, 1, v_a_2709_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2713_);
v___x_2715_ = v___x_2711_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
else
{
lean_dec(v_a_2706_);
return v___x_2708_;
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v_fvarId_2696_);
lean_dec_ref_known(v_code_2503_, 1);
v_a_2718_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2705_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2705_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v_fvarId_2696_);
lean_dec_ref_known(v_code_2503_, 1);
v_a_2726_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2701_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2701_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
else
{
lean_object* v___x_2734_; 
lean_dec(v_a_2699_);
lean_inc(v_fvarId_2696_);
v___x_2734_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_2696_, v_code_2503_, v_fvarId_2696_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec(v_fvarId_2696_);
return v___x_2734_;
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec(v_fvarId_2696_);
lean_dec_ref_known(v_code_2503_, 1);
v_a_2735_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2698_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2698_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
case 6:
{
lean_object* v_type_2743_; lean_object* v_currDeclResultType_2744_; size_t v___x_2745_; size_t v___x_2746_; uint8_t v___x_2747_; 
v_type_2743_ = lean_ctor_get(v_code_2503_, 0);
v_currDeclResultType_2744_ = lean_ctor_get(v_a_2504_, 1);
v___x_2745_ = lean_ptr_addr(v_type_2743_);
v___x_2746_ = lean_ptr_addr(v_currDeclResultType_2744_);
v___x_2747_ = lean_usize_dec_eq(v___x_2745_, v___x_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2755_; 
v_isSharedCheck_2755_ = !lean_is_exclusive(v_code_2503_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; 
v_unused_2756_ = lean_ctor_get(v_code_2503_, 0);
lean_dec(v_unused_2756_);
v___x_2749_ = v_code_2503_;
v_isShared_2750_ = v_isSharedCheck_2755_;
goto v_resetjp_2748_;
}
else
{
lean_dec(v_code_2503_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2755_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
lean_inc_ref(v_currDeclResultType_2744_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v_currDeclResultType_2744_);
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_currDeclResultType_2744_);
v___x_2752_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; 
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
return v___x_2753_;
}
}
}
else
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2757_, 0, v_code_2503_);
return v___x_2757_;
}
}
case 8:
{
lean_object* v_fvarId_2758_; lean_object* v_i_2759_; lean_object* v_y_2760_; lean_object* v_k_2761_; lean_object* v___x_2762_; 
v_fvarId_2758_ = lean_ctor_get(v_code_2503_, 0);
lean_inc(v_fvarId_2758_);
v_i_2759_ = lean_ctor_get(v_code_2503_, 1);
lean_inc(v_i_2759_);
v_y_2760_ = lean_ctor_get(v_code_2503_, 2);
lean_inc(v_y_2760_);
v_k_2761_ = lean_ctor_get(v_code_2503_, 3);
lean_inc_ref_n(v_k_2761_, 2);
v___x_2762_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2761_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___x_2762_, 1);
v___x_2764_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11);
lean_inc(v_y_2760_);
v___x_2765_ = l_Lean_Compiler_LCNF_getType(v_y_2760_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; uint8_t v___x_2767_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2765_, 1);
v___x_2767_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2766_, v___x_2764_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; 
lean_inc(v_y_2760_);
v___x_2768_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_y_2760_, v_a_2766_, v___x_2764_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; uint8_t v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2768_, 1);
v___x_2770_ = 1;
v___x_2771_ = lean_box(0);
v___x_2772_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2770_, v___x_2771_, v___x_2764_, v_a_2769_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v_fvarId_2774_; lean_object* v___x_2775_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2772_, 1);
v_fvarId_2774_ = lean_ctor_get(v_a_2773_, 0);
lean_inc(v_fvarId_2774_);
v___x_2775_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_2758_, v_i_2759_, v_a_2763_, v_y_2760_, v_k_2761_, v_code_2503_, v_fvarId_2774_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec_ref(v_k_2761_);
lean_dec(v_y_2760_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2784_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_2784_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2784_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2780_, 0, v_a_2773_);
lean_ctor_set(v___x_2780_, 1, v_a_2776_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_2780_);
v___x_2782_ = v___x_2778_;
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
else
{
lean_dec(v_a_2773_);
return v___x_2775_;
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec(v_a_2763_);
lean_dec_ref(v_k_2761_);
lean_dec(v_y_2760_);
lean_dec(v_i_2759_);
lean_dec(v_fvarId_2758_);
lean_dec_ref_known(v_code_2503_, 4);
v_a_2785_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2772_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2772_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_dec(v_a_2763_);
lean_dec_ref(v_k_2761_);
lean_dec(v_y_2760_);
lean_dec(v_i_2759_);
lean_dec(v_fvarId_2758_);
lean_dec_ref_known(v_code_2503_, 4);
v_a_2793_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2768_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2768_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
else
{
lean_object* v___x_2801_; 
lean_dec(v_a_2766_);
lean_inc(v_y_2760_);
v___x_2801_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_2758_, v_i_2759_, v_a_2763_, v_y_2760_, v_k_2761_, v_code_2503_, v_y_2760_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec_ref(v_k_2761_);
lean_dec(v_y_2760_);
return v___x_2801_;
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_a_2763_);
lean_dec_ref(v_k_2761_);
lean_dec(v_y_2760_);
lean_dec(v_i_2759_);
lean_dec(v_fvarId_2758_);
lean_dec_ref_known(v_code_2503_, 4);
v_a_2802_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2765_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2765_);
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
}
else
{
lean_dec_ref(v_k_2761_);
lean_dec(v_y_2760_);
lean_dec(v_i_2759_);
lean_dec(v_fvarId_2758_);
lean_dec_ref_known(v_code_2503_, 4);
return v___x_2762_;
}
}
case 9:
{
lean_object* v_fvarId_2810_; lean_object* v_i_2811_; lean_object* v_offset_2812_; lean_object* v_y_2813_; lean_object* v_ty_2814_; lean_object* v_k_2815_; lean_object* v___x_2816_; 
v_fvarId_2810_ = lean_ctor_get(v_code_2503_, 0);
lean_inc(v_fvarId_2810_);
v_i_2811_ = lean_ctor_get(v_code_2503_, 1);
lean_inc(v_i_2811_);
v_offset_2812_ = lean_ctor_get(v_code_2503_, 2);
lean_inc(v_offset_2812_);
v_y_2813_ = lean_ctor_get(v_code_2503_, 3);
lean_inc(v_y_2813_);
v_ty_2814_ = lean_ctor_get(v_code_2503_, 4);
lean_inc_ref(v_ty_2814_);
v_k_2815_ = lean_ctor_get(v_code_2503_, 5);
lean_inc_ref_n(v_k_2815_, 2);
v___x_2816_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2815_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
lean_inc(v_y_2813_);
v___x_2818_ = l_Lean_Compiler_LCNF_getType(v_y_2813_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; uint8_t v___x_2820_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v___x_2820_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2819_, v_ty_2814_);
if (v___x_2820_ == 0)
{
lean_object* v___x_2821_; 
lean_inc_ref(v_ty_2814_);
lean_inc(v_y_2813_);
v___x_2821_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_y_2813_, v_a_2819_, v_ty_2814_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; uint8_t v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2821_, 1);
v___x_2823_ = 1;
v___x_2824_ = lean_box(0);
lean_inc_ref(v_ty_2814_);
v___x_2825_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2823_, v___x_2824_, v_ty_2814_, v_a_2822_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v_fvarId_2827_; lean_object* v___x_2828_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v_fvarId_2827_ = lean_ctor_get(v_a_2826_, 0);
lean_inc(v_fvarId_2827_);
v___x_2828_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_2810_, v_i_2811_, v_offset_2812_, v_ty_2814_, v_a_2817_, v_y_2813_, v_k_2815_, v_code_2503_, v_fvarId_2827_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec_ref(v_k_2815_);
lean_dec(v_y_2813_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2837_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2831_ = v___x_2828_;
v_isShared_2832_ = v_isSharedCheck_2837_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2828_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2837_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2833_, 0, v_a_2826_);
lean_ctor_set(v___x_2833_, 1, v_a_2829_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v___x_2833_);
v___x_2835_ = v___x_2831_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2833_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
else
{
lean_dec(v_a_2826_);
return v___x_2828_;
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec(v_a_2817_);
lean_dec_ref(v_k_2815_);
lean_dec_ref(v_ty_2814_);
lean_dec(v_y_2813_);
lean_dec(v_offset_2812_);
lean_dec(v_i_2811_);
lean_dec(v_fvarId_2810_);
lean_dec_ref_known(v_code_2503_, 6);
v_a_2838_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2825_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2825_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec(v_a_2817_);
lean_dec_ref(v_k_2815_);
lean_dec_ref(v_ty_2814_);
lean_dec(v_y_2813_);
lean_dec(v_offset_2812_);
lean_dec(v_i_2811_);
lean_dec(v_fvarId_2810_);
lean_dec_ref_known(v_code_2503_, 6);
v_a_2846_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2821_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2821_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
else
{
lean_object* v___x_2854_; 
lean_dec(v_a_2819_);
lean_inc(v_y_2813_);
v___x_2854_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_2810_, v_i_2811_, v_offset_2812_, v_ty_2814_, v_a_2817_, v_y_2813_, v_k_2815_, v_code_2503_, v_y_2813_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec_ref(v_k_2815_);
lean_dec(v_y_2813_);
return v___x_2854_;
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v_a_2817_);
lean_dec_ref(v_k_2815_);
lean_dec_ref(v_ty_2814_);
lean_dec(v_y_2813_);
lean_dec(v_offset_2812_);
lean_dec(v_i_2811_);
lean_dec(v_fvarId_2810_);
lean_dec_ref_known(v_code_2503_, 6);
v_a_2855_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2818_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2818_);
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
else
{
lean_dec_ref(v_k_2815_);
lean_dec_ref(v_ty_2814_);
lean_dec(v_y_2813_);
lean_dec(v_offset_2812_);
lean_dec(v_i_2811_);
lean_dec(v_fvarId_2810_);
lean_dec_ref_known(v_code_2503_, 6);
return v___x_2816_;
}
}
default: 
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_dec_ref(v_code_2503_);
v___x_2863_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2);
v___x_2864_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2863_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
return v___x_2864_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed(lean_object* v_code_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_code_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
lean_dec(v_a_2867_);
lean_dec_ref(v_a_2866_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(lean_object* v_i_2874_, lean_object* v_as_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v___x_2883_; uint8_t v___x_2884_; 
v___x_2883_ = lean_array_get_size(v_as_2875_);
v___x_2884_ = lean_nat_dec_lt(v_i_2874_, v___x_2883_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; 
lean_dec(v_i_2874_);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_as_2875_);
return v___x_2885_;
}
else
{
lean_object* v___f_2886_; lean_object* v_a_2887_; lean_object* v___x_2888_; 
v___f_2886_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed), 8, 0);
v_a_2887_ = lean_array_fget_borrowed(v_as_2875_, v_i_2874_);
lean_inc(v_a_2887_);
v___x_2888_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_a_2887_, v___f_2886_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; size_t v___x_2890_; size_t v___x_2891_; uint8_t v___x_2892_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v___x_2888_, 1);
v___x_2890_ = lean_ptr_addr(v_a_2887_);
v___x_2891_ = lean_ptr_addr(v_a_2889_);
v___x_2892_ = lean_usize_dec_eq(v___x_2890_, v___x_2891_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2893_ = lean_unsigned_to_nat(1u);
v___x_2894_ = lean_nat_add(v_i_2874_, v___x_2893_);
v___x_2895_ = lean_array_fset(v_as_2875_, v_i_2874_, v_a_2889_);
lean_dec(v_i_2874_);
v_i_2874_ = v___x_2894_;
v_as_2875_ = v___x_2895_;
goto _start;
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
lean_dec(v_a_2889_);
v___x_2897_ = lean_unsigned_to_nat(1u);
v___x_2898_ = lean_nat_add(v_i_2874_, v___x_2897_);
lean_dec(v_i_2874_);
v_i_2874_ = v___x_2898_;
goto _start;
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec_ref(v_as_2875_);
lean_dec(v_i_2874_);
v_a_2900_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2888_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2888_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3___boxed(lean_object* v_i_2908_, lean_object* v_as_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(v_i_2908_, v_as_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___boxed(lean_object* v_code_2918_, lean_object* v_decl_2919_, lean_object* v_k_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(v_code_2918_, v_decl_2919_, v_k_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec(v_a_2926_);
lean_dec_ref(v_a_2925_);
lean_dec(v_a_2924_);
lean_dec_ref(v_a_2923_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(uint8_t v_pu_2929_, lean_object* v_alt_2930_, lean_object* v_f_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_alt_2930_, v_f_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___boxed(lean_object* v_pu_2940_, lean_object* v_alt_2941_, lean_object* v_f_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
uint8_t v_pu_boxed_2950_; lean_object* v_res_2951_; 
v_pu_boxed_2950_ = lean_unbox(v_pu_2940_);
v_res_2951_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(v_pu_boxed_2950_, v_alt_2941_, v_f_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(lean_object* v_as_2955_, size_t v_i_2956_, size_t v_stop_2957_, lean_object* v_b_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_a_2965_; uint8_t v___x_2969_; 
v___x_2969_ = lean_usize_dec_eq(v_i_2956_, v_stop_2957_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; lean_object* v_value_2971_; 
v___x_2970_ = lean_array_uget(v_as_2955_, v_i_2956_);
v_value_2971_ = lean_ctor_get(v___x_2970_, 1);
lean_inc_ref(v_value_2971_);
if (lean_obj_tag(v_value_2971_) == 0)
{
lean_object* v_toSignature_2972_; uint8_t v_recursive_2973_; lean_object* v_inlineAttr_x3f_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_3019_; 
v_toSignature_2972_ = lean_ctor_get(v___x_2970_, 0);
v_recursive_2973_ = lean_ctor_get_uint8(v___x_2970_, sizeof(void*)*3);
v_inlineAttr_x3f_2974_ = lean_ctor_get(v___x_2970_, 2);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; 
v_unused_3020_ = lean_ctor_get(v___x_2970_, 1);
lean_dec(v_unused_3020_);
v___x_2976_ = v___x_2970_;
v_isShared_2977_ = v_isSharedCheck_3019_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_inlineAttr_x3f_2974_);
lean_inc(v_toSignature_2972_);
lean_dec(v___x_2970_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_3019_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v_code_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3018_; 
v_code_2978_ = lean_ctor_get(v_value_2971_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_value_2971_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_2980_ = v_value_2971_;
v_isShared_2981_ = v_isSharedCheck_3018_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_code_2978_);
lean_dec(v_value_2971_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3018_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v_name_2982_; lean_object* v_type_2983_; lean_object* v_s_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v_name_2982_ = lean_ctor_get(v_toSignature_2972_, 0);
v_type_2983_ = lean_ctor_get(v_toSignature_2972_, 2);
lean_inc_ref(v_type_2983_);
lean_inc(v_name_2982_);
v_s_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_2984_, 0, v_name_2982_);
lean_ctor_set(v_s_2984_, 1, v_type_2983_);
v___x_2985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0));
v___x_2986_ = lean_st_mk_ref(v___x_2985_);
v___x_2987_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_code_2978_, v_s_2984_, v___x_2986_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec_ref_known(v_s_2984_, 2);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2989_; lean_object* v_auxDecls_2990_; lean_object* v___x_2991_; uint8_t v___x_2992_; lean_object* v___x_2994_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v___x_2987_, 1);
v___x_2989_ = lean_st_ref_get(v___x_2986_);
lean_dec(v___x_2986_);
v_auxDecls_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc_ref(v_auxDecls_2990_);
lean_dec(v___x_2989_);
v___x_2991_ = l_Array_append___redArg(v_b_2958_, v_auxDecls_2990_);
lean_dec_ref(v_auxDecls_2990_);
v___x_2992_ = 1;
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v_a_2988_);
v___x_2994_ = v___x_2980_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_2988_);
v___x_2994_ = v_reuseFailAlloc_3009_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2996_; 
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 1, v___x_2994_);
v___x_2996_ = v___x_2976_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_toSignature_2972_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v_inlineAttr_x3f_2974_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, sizeof(void*)*3, v_recursive_2973_);
v___x_2996_ = v_reuseFailAlloc_3008_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_2992_, v___x_2996_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v___x_2999_ = lean_array_push(v___x_2991_, v_a_2998_);
v_a_2965_ = v___x_2999_;
goto v___jp_2964_;
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec_ref(v___x_2991_);
v_a_3000_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2997_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2997_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec(v___x_2986_);
lean_del_object(v___x_2980_);
lean_del_object(v___x_2976_);
lean_dec(v_inlineAttr_x3f_2974_);
lean_dec_ref(v_toSignature_2972_);
lean_dec_ref(v_b_2958_);
v_a_3010_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_2987_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_2987_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
}
else
{
lean_object* v___x_3021_; 
lean_dec_ref_known(v_value_2971_, 1);
v___x_3021_ = lean_array_push(v_b_2958_, v___x_2970_);
v_a_2965_ = v___x_3021_;
goto v___jp_2964_;
}
}
else
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3022_, 0, v_b_2958_);
return v___x_3022_;
}
v___jp_2964_:
{
size_t v___x_2966_; size_t v___x_2967_; 
v___x_2966_ = ((size_t)1ULL);
v___x_2967_ = lean_usize_add(v_i_2956_, v___x_2966_);
v_i_2956_ = v___x_2967_;
v_b_2958_ = v_a_2965_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___boxed(lean_object* v_as_3023_, lean_object* v_i_3024_, lean_object* v_stop_3025_, lean_object* v_b_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
size_t v_i_boxed_3032_; size_t v_stop_boxed_3033_; lean_object* v_res_3034_; 
v_i_boxed_3032_ = lean_unbox_usize(v_i_3024_);
lean_dec(v_i_3024_);
v_stop_boxed_3033_ = lean_unbox_usize(v_stop_3025_);
lean_dec(v_stop_3025_);
v_res_3034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_as_3023_, v_i_boxed_3032_, v_stop_boxed_3033_, v_b_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec_ref(v_as_3023_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(lean_object* v_decls_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
v___x_3041_ = lean_unsigned_to_nat(0u);
v___x_3042_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0));
v___x_3043_ = lean_array_get_size(v_decls_3035_);
v___x_3044_ = lean_nat_dec_lt(v___x_3041_, v___x_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; 
v___x_3045_ = l_Lean_Compiler_LCNF_addBoxedVersions(v___x_3042_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
return v___x_3045_;
}
else
{
size_t v___x_3046_; size_t v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = ((size_t)0ULL);
v___x_3047_ = lean_usize_of_nat(v___x_3043_);
v___x_3048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_decls_3035_, v___x_3046_, v___x_3047_, v___x_3042_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3050_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v___x_3050_ = l_Lean_Compiler_LCNF_addBoxedVersions(v_a_3049_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
return v___x_3050_;
}
else
{
return v___x_3048_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run___boxed(lean_object* v_decls_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(v_decls_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec_ref(v_decls_3051_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3139_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_));
v___x_3140_ = 1;
v___x_3141_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_));
v___x_3142_ = l_Lean_registerTraceClass(v___x_3139_, v___x_3140_, v___x_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2____boxed(lean_object* v_a_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_();
return v_res_3144_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_AuxDeclCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Runtime(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
