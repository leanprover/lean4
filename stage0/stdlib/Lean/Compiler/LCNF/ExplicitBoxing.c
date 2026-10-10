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
lean_object* l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_CtorInfo_isScalar(lean_object*);
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
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1_ = stack[0].m_obj;
size_t v_i_2_ = stack[1].m_num;
size_t v_stop_3_ = stack[2].m_num;
uint8_t v_res_18_;
v_res_18_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(v_as_1_, v_i_2_, v_stop_3_);
stack->m_num = v_res_18_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0___boxed(lean_object* v_as_19_, lean_object* v_i_20_, lean_object* v_stop_21_){
_start:
{
size_t v_i_boxed_22_; size_t v_stop_boxed_23_; uint8_t v_res_24_; lean_object* v_r_25_; 
v_i_boxed_22_ = lean_unbox_usize(v_i_20_);
lean_dec(v_i_20_);
v_stop_boxed_23_ = lean_unbox_usize(v_stop_21_);
lean_dec(v_stop_21_);
v_res_24_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(v_as_19_, v_i_boxed_22_, v_stop_boxed_23_);
lean_dec_ref(v_as_19_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(lean_object* v_sig_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_name_29_; lean_object* v_type_30_; lean_object* v_params_31_; lean_object* v___x_32_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v_name_29_ = lean_ctor_get(v_sig_26_, 0);
lean_inc(v_name_29_);
v_type_30_ = lean_ctor_get(v_sig_26_, 2);
lean_inc_ref(v_type_30_);
v_params_31_ = lean_ctor_get(v_sig_26_, 3);
lean_inc_ref(v_params_31_);
lean_dec_ref(v_sig_26_);
v___x_32_ = lean_st_ref_get(v_a_27_);
v___x_39_ = lean_unsigned_to_nat(0u);
v___x_40_ = lean_array_get_size(v_params_31_);
v___x_41_ = lean_nat_dec_lt(v___x_39_, v___x_40_);
if (v___x_41_ == 0)
{
lean_dec(v___x_32_);
lean_dec_ref(v_type_30_);
lean_dec(v_name_29_);
goto v___jp_33_;
}
else
{
lean_object* v_env_42_; uint8_t v___y_48_; uint8_t v___x_51_; 
v_env_42_ = lean_ctor_get(v___x_32_, 0);
lean_inc_ref(v_env_42_);
lean_dec(v___x_32_);
v___x_51_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_30_);
lean_dec_ref(v_type_30_);
if (v___x_51_ == 0)
{
if (v___x_41_ == 0)
{
goto v___jp_43_;
}
else
{
if (v___x_41_ == 0)
{
goto v___jp_43_;
}
else
{
size_t v___x_52_; size_t v___x_53_; uint8_t v___x_54_; 
v___x_52_ = ((size_t)0ULL);
v___x_53_ = lean_usize_of_nat(v___x_40_);
v___x_54_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(v_params_31_, v___x_52_, v___x_53_);
v___y_48_ = v___x_54_;
goto v___jp_47_;
}
}
}
else
{
v___y_48_ = v___x_51_;
goto v___jp_47_;
}
v___jp_43_:
{
uint8_t v___x_44_; 
v___x_44_ = l_Lean_isExtern(v_env_42_, v_name_29_);
if (v___x_44_ == 0)
{
goto v___jp_33_;
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_dec_ref(v_params_31_);
v___x_45_ = lean_box(v___x_44_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
}
v___jp_47_:
{
if (v___y_48_ == 0)
{
goto v___jp_43_;
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec_ref(v_env_42_);
lean_dec_ref(v_params_31_);
lean_dec(v_name_29_);
v___x_49_ = lean_box(v___y_48_);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
}
v___jp_33_:
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
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_sig_26_ = stack[0].m_obj;
lean_object* v_a_27_ = stack[1].m_obj;
lean_object* v_res_55_;
v_res_55_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_sig_26_, v_a_27_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg___boxed(lean_object* v_sig_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_sig_56_, v_a_57_);
lean_dec(v_a_57_);
return v_res_59_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion(lean_object* v_sig_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_sig_60_, v_a_64_);
return v___x_66_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_0interp(lean_interpreter_value* stack)
{
lean_object* v_sig_60_ = stack[0].m_obj;
lean_object* v_a_61_ = stack[1].m_obj;
lean_object* v_a_62_ = stack[2].m_obj;
lean_object* v_a_63_ = stack[3].m_obj;
lean_object* v_a_64_ = stack[4].m_obj;
lean_object* v_res_67_;
v_res_67_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion(v_sig_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
stack->m_obj
 = v_res_67_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___boxed(lean_object* v_sig_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion(v_sig_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
return v_res_74_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(size_t v_sz_75_, size_t v_i_76_, lean_object* v_bs_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
uint8_t v___x_83_; 
v___x_83_ = lean_usize_dec_lt(v_i_76_, v_sz_75_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v_bs_77_);
return v___x_84_;
}
else
{
lean_object* v_v_85_; lean_object* v_binderName_86_; lean_object* v_type_87_; lean_object* v___x_88_; lean_object* v_bs_x27_89_; uint8_t v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; 
v_v_85_ = lean_array_uget_borrowed(v_bs_77_, v_i_76_);
v_binderName_86_ = lean_ctor_get(v_v_85_, 1);
lean_inc(v_binderName_86_);
v_type_87_ = lean_ctor_get(v_v_85_, 2);
lean_inc_ref(v_type_87_);
v___x_88_ = lean_unsigned_to_nat(0u);
v_bs_x27_89_ = lean_array_uset(v_bs_77_, v_i_76_, v___x_88_);
v___x_90_ = 1;
v___x_91_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_87_);
lean_dec_ref(v_type_87_);
v___x_92_ = 0;
v___x_93_ = l_Lean_Compiler_LCNF_mkParam(v___x_90_, v_binderName_86_, v___x_91_, v___x_92_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; size_t v___x_95_; size_t v___x_96_; lean_object* v___x_97_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_a_94_);
lean_dec_ref_known(v___x_93_, 1);
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_add(v_i_76_, v___x_95_);
v___x_97_ = lean_array_uset(v_bs_x27_89_, v_i_76_, v_a_94_);
v_i_76_ = v___x_96_;
v_bs_77_ = v___x_97_;
goto _start;
}
else
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
lean_dec_ref(v_bs_x27_89_);
v_a_99_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_93_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_93_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_75_ = stack[0].m_num;
size_t v_i_76_ = stack[1].m_num;
lean_object* v_bs_77_ = stack[2].m_obj;
lean_object* v___y_78_ = stack[3].m_obj;
lean_object* v___y_79_ = stack[4].m_obj;
lean_object* v___y_80_ = stack[5].m_obj;
lean_object* v___y_81_ = stack[6].m_obj;
lean_object* v_res_107_;
v_res_107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(v_sz_75_, v_i_76_, v_bs_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
stack->m_obj
 = v_res_107_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0___boxed(lean_object* v_sz_108_, lean_object* v_i_109_, lean_object* v_bs_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
size_t v_sz_boxed_116_; size_t v_i_boxed_117_; lean_object* v_res_118_; 
v_sz_boxed_116_ = lean_unbox_usize(v_sz_108_);
lean_dec(v_sz_108_);
v_i_boxed_117_ = lean_unbox_usize(v_i_109_);
lean_dec(v_i_109_);
v_res_118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(v_sz_boxed_116_, v_i_boxed_117_, v_bs_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_118_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(lean_object* v_as_120_, size_t v_sz_121_, size_t v_i_122_, lean_object* v_b_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_a_130_; uint8_t v___x_134_; 
v___x_134_ = lean_usize_dec_lt(v_i_122_, v_sz_121_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v_b_123_);
return v___x_135_;
}
else
{
lean_object* v_snd_136_; lean_object* v_snd_137_; lean_object* v_fst_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_211_; 
v_snd_136_ = lean_ctor_get(v_b_123_, 1);
lean_inc(v_snd_136_);
v_snd_137_ = lean_ctor_get(v_snd_136_, 1);
lean_inc(v_snd_137_);
v_fst_138_ = lean_ctor_get(v_b_123_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v_b_123_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_b_123_, 1);
lean_dec(v_unused_212_);
v___x_140_ = v_b_123_;
v_isShared_141_ = v_isSharedCheck_211_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_fst_138_);
lean_dec(v_b_123_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_211_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v_fst_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_209_; 
v_fst_142_ = lean_ctor_get(v_snd_136_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v_snd_136_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v_snd_136_, 1);
lean_dec(v_unused_210_);
v___x_144_ = v_snd_136_;
v_isShared_145_ = v_isSharedCheck_209_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_fst_142_);
lean_dec(v_snd_136_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_209_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v_array_146_; lean_object* v_start_147_; lean_object* v_stop_148_; uint8_t v___x_149_; 
v_array_146_ = lean_ctor_get(v_snd_137_, 0);
v_start_147_ = lean_ctor_get(v_snd_137_, 1);
v_stop_148_ = lean_ctor_get(v_snd_137_, 2);
v___x_149_ = lean_nat_dec_lt(v_start_147_, v_stop_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_151_; 
if (v_isShared_145_ == 0)
{
v___x_151_ = v___x_144_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_fst_142_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_snd_137_);
v___x_151_ = v_reuseFailAlloc_156_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_153_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_151_);
v___x_153_ = v___x_140_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_fst_138_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v___x_151_);
v___x_153_ = v_reuseFailAlloc_155_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; 
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
}
else
{
lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_205_; 
lean_inc(v_stop_148_);
lean_inc(v_start_147_);
lean_inc_ref(v_array_146_);
v_isSharedCheck_205_ = !lean_is_exclusive(v_snd_137_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; lean_object* v_unused_207_; lean_object* v_unused_208_; 
v_unused_206_ = lean_ctor_get(v_snd_137_, 2);
lean_dec(v_unused_206_);
v_unused_207_ = lean_ctor_get(v_snd_137_, 1);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_snd_137_, 0);
lean_dec(v_unused_208_);
v___x_158_ = v_snd_137_;
v_isShared_159_ = v_isSharedCheck_205_;
goto v_resetjp_157_;
}
else
{
lean_dec(v_snd_137_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_205_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v_a_160_; lean_object* v_binderName_161_; lean_object* v_type_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v_a_160_ = lean_array_uget_borrowed(v_as_120_, v_i_122_);
v_binderName_161_ = lean_ctor_get(v_a_160_, 1);
v_type_162_ = lean_ctor_get(v_a_160_, 2);
v___x_163_ = lean_array_fget(v_array_146_, v_start_147_);
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = lean_nat_add(v_start_147_, v___x_164_);
lean_dec(v_start_147_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_165_);
v___x_167_ = v___x_158_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_array_146_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_stop_148_);
v___x_167_ = v_reuseFailAlloc_204_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
uint8_t v___x_168_; 
v___x_168_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_162_);
if (v___x_168_ == 0)
{
lean_object* v_fvarId_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v_fvarId_169_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_fvarId_169_);
lean_dec(v___x_163_);
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v_fvarId_169_);
v___x_171_ = lean_array_push(v_fst_142_, v___x_170_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 1, v___x_167_);
lean_ctor_set(v___x_144_, 0, v___x_171_);
v___x_173_ = v___x_144_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_167_);
v___x_173_ = v_reuseFailAlloc_177_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_175_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_173_);
v___x_175_ = v___x_140_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_fst_138_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
v_a_130_ = v___x_175_;
goto v___jp_129_;
}
}
}
else
{
lean_object* v_fvarId_178_; uint8_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_fvarId_178_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_fvarId_178_);
lean_dec(v___x_163_);
v___x_179_ = 1;
v___x_180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0));
lean_inc(v_binderName_161_);
v___x_181_ = l_Lean_Name_str___override(v_binderName_161_, v___x_180_);
v___x_182_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_182_, 0, v_fvarId_178_);
lean_inc_ref(v_type_162_);
v___x_183_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_179_, v___x_181_, v_type_162_, v___x_182_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v_fvarId_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref_known(v___x_183_, 1);
v_fvarId_185_ = lean_ctor_get(v_a_184_, 0);
lean_inc(v_fvarId_185_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v_a_184_);
v___x_187_ = lean_array_push(v_fst_138_, v___x_186_);
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v_fvarId_185_);
v___x_189_ = lean_array_push(v_fst_142_, v___x_188_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 1, v___x_167_);
lean_ctor_set(v___x_144_, 0, v___x_189_);
v___x_191_ = v___x_144_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_167_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_193_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_191_);
lean_ctor_set(v___x_140_, 0, v___x_187_);
v___x_193_ = v___x_140_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
v_a_130_ = v___x_193_;
goto v___jp_129_;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec_ref(v___x_167_);
lean_del_object(v___x_144_);
lean_dec(v_fst_142_);
lean_del_object(v___x_140_);
lean_dec(v_fst_138_);
v_a_196_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_183_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_183_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
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
v___jp_129_:
{
size_t v___x_131_; size_t v___x_132_; 
v___x_131_ = ((size_t)1ULL);
v___x_132_ = lean_usize_add(v_i_122_, v___x_131_);
v_i_122_ = v___x_132_;
v_b_123_ = v_a_130_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_120_ = stack[0].m_obj;
size_t v_sz_121_ = stack[1].m_num;
size_t v_i_122_ = stack[2].m_num;
lean_object* v_b_123_ = stack[3].m_obj;
lean_object* v___y_124_ = stack[4].m_obj;
lean_object* v___y_125_ = stack[5].m_obj;
lean_object* v___y_126_ = stack[6].m_obj;
lean_object* v___y_127_ = stack[7].m_obj;
lean_object* v_res_213_;
v_res_213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(v_as_120_, v_sz_121_, v_i_122_, v_b_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
stack->m_obj
 = v_res_213_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___boxed(lean_object* v_as_214_, lean_object* v_sz_215_, lean_object* v_i_216_, lean_object* v_b_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
size_t v_sz_boxed_223_; size_t v_i_boxed_224_; lean_object* v_res_225_; 
v_sz_boxed_223_ = lean_unbox_usize(v_sz_215_);
lean_dec(v_sz_215_);
v_i_boxed_224_ = lean_unbox_usize(v_i_216_);
lean_dec(v_i_216_);
v_res_225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(v_as_214_, v_sz_boxed_223_, v_i_boxed_224_, v_b_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec_ref(v_as_214_);
return v_res_225_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(lean_object* v_sig_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_name_240_; lean_object* v_type_241_; lean_object* v_params_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_361_; 
v_name_240_ = lean_ctor_get(v_sig_234_, 0);
v_type_241_ = lean_ctor_get(v_sig_234_, 2);
v_params_242_ = lean_ctor_get(v_sig_234_, 3);
v_isSharedCheck_361_ = !lean_is_exclusive(v_sig_234_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; 
v_unused_362_ = lean_ctor_get(v_sig_234_, 1);
lean_dec(v_unused_362_);
v___x_244_ = v_sig_234_;
v_isShared_245_ = v_isSharedCheck_361_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_params_242_);
lean_inc(v_type_241_);
lean_inc(v_name_240_);
lean_dec(v_sig_234_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_361_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
size_t v_sz_246_; size_t v___x_247_; lean_object* v___x_248_; 
v_sz_246_ = lean_array_size(v_params_242_);
v___x_247_ = ((size_t)0ULL);
lean_inc_ref(v_params_242_);
v___x_248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(v_sz_246_, v___x_247_, v_params_242_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v_value_251_; lean_object* v___y_252_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc_n(v_a_249_, 2);
lean_dec_ref_known(v___x_248_, 1);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0));
v___x_283_ = lean_array_get_size(v_params_242_);
v___x_284_ = lean_mk_empty_array_with_capacity(v___x_283_);
v___x_285_ = lean_array_get_size(v_a_249_);
v___x_286_ = l_Array_toSubarray___redArg(v_a_249_, v___x_281_, v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_284_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_282_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(v_params_242_, v_sz_246_, v___x_247_, v___x_288_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec_ref(v_params_242_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v_snd_291_; lean_object* v_fst_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_344_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
lean_dec_ref_known(v___x_289_, 1);
v_snd_291_ = lean_ctor_get(v_a_290_, 1);
v_fst_292_ = lean_ctor_get(v_a_290_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v_a_290_);
if (v_isSharedCheck_344_ == 0)
{
v___x_294_ = v_a_290_;
v_isShared_295_ = v_isSharedCheck_344_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_snd_291_);
lean_inc(v_fst_292_);
lean_dec(v_a_290_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_344_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v_fst_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_342_; 
v_fst_296_ = lean_ctor_get(v_snd_291_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v_snd_291_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; 
v_unused_343_ = lean_ctor_get(v_snd_291_, 1);
lean_dec(v_unused_343_);
v___x_298_ = v_snd_291_;
v_isShared_299_ = v_isSharedCheck_342_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_fst_296_);
lean_dec(v_snd_291_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_342_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_300_ = 1;
v___x_301_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2));
lean_inc(v_name_240_);
if (v_isShared_299_ == 0)
{
lean_ctor_set_tag(v___x_298_, 9);
lean_ctor_set(v___x_298_, 1, v_fst_296_);
lean_ctor_set(v___x_298_, 0, v_name_240_);
v___x_303_ = v___x_298_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_name_240_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_fst_296_);
v___x_303_ = v_reuseFailAlloc_341_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; 
lean_inc_ref(v_type_241_);
v___x_304_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_300_, v___x_301_, v_type_241_, v___x_303_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc_n(v_a_305_, 2);
lean_dec_ref_known(v___x_304_, 1);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v_a_305_);
v___x_307_ = lean_array_push(v_fst_292_, v___x_306_);
v___x_308_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_241_);
if (v___x_308_ == 0)
{
lean_object* v_fvarId_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
lean_del_object(v___x_294_);
v_fvarId_309_ = lean_ctor_get(v_a_305_, 0);
lean_inc(v_fvarId_309_);
lean_dec(v_a_305_);
v___x_310_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_310_, 0, v_fvarId_309_);
v___x_311_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___x_307_, v___x_310_);
lean_dec_ref(v___x_307_);
v_value_251_ = v___x_311_;
v___y_252_ = v_a_238_;
goto v___jp_250_;
}
else
{
lean_object* v_fvarId_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v_fvarId_312_ = lean_ctor_get(v_a_305_, 0);
lean_inc(v_fvarId_312_);
lean_dec(v_a_305_);
v___x_313_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4));
v___x_314_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_241_);
lean_inc_ref(v_type_241_);
if (v_isShared_295_ == 0)
{
lean_ctor_set_tag(v___x_294_, 13);
lean_ctor_set(v___x_294_, 1, v_fvarId_312_);
lean_ctor_set(v___x_294_, 0, v_type_241_);
v___x_316_ = v___x_294_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_type_241_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_fvarId_312_);
v___x_316_ = v_reuseFailAlloc_332_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_300_, v___x_313_, v___x_314_, v___x_316_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v_fvarId_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
v_fvarId_319_ = lean_ctor_get(v_a_318_, 0);
lean_inc(v_fvarId_319_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v_a_318_);
v___x_321_ = lean_array_push(v___x_307_, v___x_320_);
v___x_322_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_322_, 0, v_fvarId_319_);
v___x_323_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___x_321_, v___x_322_);
lean_dec_ref(v___x_321_);
v_value_251_ = v___x_323_;
v___y_252_ = v_a_238_;
goto v___jp_250_;
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v___x_307_);
lean_dec(v_a_249_);
lean_del_object(v___x_244_);
lean_dec_ref(v_type_241_);
lean_dec(v_name_240_);
v_a_324_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_317_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_317_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_del_object(v___x_294_);
lean_dec(v_fst_292_);
lean_dec(v_a_249_);
lean_del_object(v___x_244_);
lean_dec_ref(v_type_241_);
lean_dec(v_name_240_);
v_a_333_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_304_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_304_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_a_249_);
lean_del_object(v___x_244_);
lean_dec_ref(v_type_241_);
lean_dec(v_name_240_);
v_a_345_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_289_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_289_);
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
v___jp_250_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; lean_object* v___x_258_; 
v___x_253_ = l_Lean_Compiler_LCNF_mkBoxedName(v_name_240_);
v___x_254_ = lean_box(0);
v___x_255_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_241_);
lean_dec_ref(v_type_241_);
v___x_256_ = 1;
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 3, v_a_249_);
lean_ctor_set(v___x_244_, 2, v___x_255_);
lean_ctor_set(v___x_244_, 1, v___x_254_);
lean_ctor_set(v___x_244_, 0, v___x_253_);
v___x_258_ = v___x_244_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_280_, 3, v_a_249_);
v___x_258_ = v_reuseFailAlloc_280_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*4, v___x_256_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_value_251_);
v___x_260_ = 0;
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_262_, 0, v___x_258_);
lean_ctor_set(v___x_262_, 1, v___x_259_);
lean_ctor_set(v___x_262_, 2, v___x_261_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*3, v___x_260_);
lean_inc_ref(v___x_262_);
v___x_263_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v___x_262_, v___y_252_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; 
v_unused_271_ = lean_ctor_get(v___x_263_, 0);
lean_dec(v_unused_271_);
v___x_265_ = v___x_263_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_dec(v___x_263_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_262_);
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_262_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_dec_ref_known(v___x_262_, 3);
v_a_272_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_263_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_263_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_del_object(v___x_244_);
lean_dec_ref(v_params_242_);
lean_dec_ref(v_type_241_);
lean_dec(v_name_240_);
v_a_353_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_248_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_248_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_0interp(lean_interpreter_value* stack)
{
lean_object* v_sig_234_ = stack[0].m_obj;
lean_object* v_a_235_ = stack[1].m_obj;
lean_object* v_a_236_ = stack[2].m_obj;
lean_object* v_a_237_ = stack[3].m_obj;
lean_object* v_a_238_ = stack[4].m_obj;
lean_object* v_res_363_;
v_res_363_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(v_sig_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
stack->m_obj
 = v_res_363_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___boxed(lean_object* v_sig_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(v_sig_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
return v_res_370_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(lean_object* v_as_371_, size_t v_i_372_, size_t v_stop_373_, lean_object* v_b_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_a_381_; uint8_t v___x_385_; 
v___x_385_ = lean_usize_dec_eq(v_i_372_, v_stop_373_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v_toSignature_387_; lean_object* v___x_388_; 
v___x_386_ = lean_array_uget_borrowed(v_as_371_, v_i_372_);
v_toSignature_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc_ref(v_toSignature_387_);
v___x_388_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_toSignature_387_, v___y_378_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; uint8_t v___x_390_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
v___x_390_ = lean_unbox(v_a_389_);
lean_dec(v_a_389_);
if (v___x_390_ == 0)
{
v_a_381_ = v_b_374_;
goto v___jp_380_;
}
else
{
lean_object* v___x_391_; 
lean_inc_ref(v_toSignature_387_);
v___x_391_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(v_toSignature_387_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_393_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_391_, 1);
v___x_393_ = lean_array_push(v_b_374_, v_a_392_);
v_a_381_ = v___x_393_;
goto v___jp_380_;
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec_ref(v_b_374_);
v_a_394_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_391_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_391_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec_ref(v_b_374_);
v_a_402_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_388_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_388_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v_b_374_);
return v___x_410_;
}
v___jp_380_:
{
size_t v___x_382_; size_t v___x_383_; 
v___x_382_ = ((size_t)1ULL);
v___x_383_ = lean_usize_add(v_i_372_, v___x_382_);
v_i_372_ = v___x_383_;
v_b_374_ = v_a_381_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_371_ = stack[0].m_obj;
size_t v_i_372_ = stack[1].m_num;
size_t v_stop_373_ = stack[2].m_num;
lean_object* v_b_374_ = stack[3].m_obj;
lean_object* v___y_375_ = stack[4].m_obj;
lean_object* v___y_376_ = stack[5].m_obj;
lean_object* v___y_377_ = stack[6].m_obj;
lean_object* v___y_378_ = stack[7].m_obj;
lean_object* v_res_411_;
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_371_, v_i_372_, v_stop_373_, v_b_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
stack->m_obj
 = v_res_411_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0___boxed(lean_object* v_as_412_, lean_object* v_i_413_, lean_object* v_stop_414_, lean_object* v_b_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
size_t v_i_boxed_421_; size_t v_stop_boxed_422_; lean_object* v_res_423_; 
v_i_boxed_421_ = lean_unbox_usize(v_i_413_);
lean_dec(v_i_413_);
v_stop_boxed_422_ = lean_unbox_usize(v_stop_414_);
lean_dec(v_stop_414_);
v_res_423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_412_, v_i_boxed_421_, v_stop_boxed_422_, v_b_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec_ref(v_as_412_);
return v_res_423_;
}
}
lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(lean_object* v_as_426_, lean_object* v_start_427_, lean_object* v_stop_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0));
v___x_435_ = lean_nat_dec_lt(v_start_427_, v_stop_428_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
return v___x_436_;
}
else
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_array_get_size(v_as_426_);
v___x_438_ = lean_nat_dec_le(v_stop_428_, v___x_437_);
if (v___x_438_ == 0)
{
uint8_t v___x_439_; 
v___x_439_ = lean_nat_dec_lt(v_start_427_, v___x_437_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_434_);
return v___x_440_;
}
else
{
size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_usize_of_nat(v_start_427_);
v___x_442_ = lean_usize_of_nat(v___x_437_);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_426_, v___x_441_, v___x_442_, v___x_434_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
return v___x_443_;
}
}
else
{
size_t v___x_444_; size_t v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_usize_of_nat(v_start_427_);
v___x_445_ = lean_usize_of_nat(v_stop_428_);
v___x_446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(v_as_426_, v___x_444_, v___x_445_, v___x_434_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT void l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_426_ = stack[0].m_obj;
lean_object* v_start_427_ = stack[1].m_obj;
lean_object* v_stop_428_ = stack[2].m_obj;
lean_object* v___y_429_ = stack[3].m_obj;
lean_object* v___y_430_ = stack[4].m_obj;
lean_object* v___y_431_ = stack[5].m_obj;
lean_object* v___y_432_ = stack[6].m_obj;
lean_object* v_res_447_;
v_res_447_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(v_as_426_, v_start_427_, v_stop_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___boxed(lean_object* v_as_448_, lean_object* v_start_449_, lean_object* v_stop_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(v_as_448_, v_start_449_, v_stop_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v_stop_450_);
lean_dec(v_start_449_);
lean_dec_ref(v_as_448_);
return v_res_456_;
}
}
lean_object* l_Lean_Compiler_LCNF_addBoxedVersions(lean_object* v_decls_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_array_get_size(v_decls_457_);
v___x_465_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(v_decls_457_, v___x_463_, v___x_464_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_474_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_474_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = l_Array_append___redArg(v_decls_457_, v_a_466_);
lean_dec(v_a_466_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
else
{
lean_dec_ref(v_decls_457_);
return v___x_465_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_addBoxedVersions_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_457_ = stack[0].m_obj;
lean_object* v_a_458_ = stack[1].m_obj;
lean_object* v_a_459_ = stack[2].m_obj;
lean_object* v_a_460_ = stack[3].m_obj;
lean_object* v_a_461_ = stack[4].m_obj;
lean_object* v_res_475_;
v_res_475_ = l_Lean_Compiler_LCNF_addBoxedVersions(v_decls_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
stack->m_obj
 = v_res_475_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addBoxedVersions___boxed(lean_object* v_decls_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Compiler_LCNF_addBoxedVersions(v_decls_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
return v_res_482_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(lean_object* v_a_483_){
_start:
{
lean_object* v_currDeclResultType_485_; lean_object* v___x_486_; 
v_currDeclResultType_485_ = lean_ctor_get(v_a_483_, 1);
lean_inc_ref(v_currDeclResultType_485_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v_currDeclResultType_485_);
return v___x_486_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_483_ = stack[0].m_obj;
lean_object* v_res_487_;
v_res_487_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(v_a_483_);
stack->m_obj
 = v_res_487_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg___boxed(lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(v_a_488_);
lean_dec_ref(v_a_488_);
return v_res_490_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_currDeclResultType_498_; lean_object* v___x_499_; 
v_currDeclResultType_498_ = lean_ctor_get(v_a_491_, 1);
lean_inc_ref(v_currDeclResultType_498_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v_currDeclResultType_498_);
return v___x_499_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_491_ = stack[0].m_obj;
lean_object* v_a_492_ = stack[1].m_obj;
lean_object* v_a_493_ = stack[2].m_obj;
lean_object* v_a_494_ = stack[3].m_obj;
lean_object* v_a_495_ = stack[4].m_obj;
lean_object* v_a_496_ = stack[5].m_obj;
lean_object* v_res_500_;
v_res_500_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
stack->m_obj
 = v_res_500_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___boxed(lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_508_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(lean_object* v_t_u2081_509_, lean_object* v_t_u2082_510_){
_start:
{
uint8_t v___y_512_; uint8_t v___y_516_; uint8_t v___x_517_; uint8_t v___x_518_; 
v___x_517_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2081_509_);
v___x_518_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2082_510_);
if (v___x_518_ == 0)
{
if (v___x_517_ == 0)
{
uint8_t v___x_519_; 
v___x_519_ = 1;
v___y_512_ = v___x_519_;
goto v___jp_511_;
}
else
{
v___y_516_ = v___x_518_;
goto v___jp_515_;
}
}
else
{
v___y_516_ = v___x_517_;
goto v___jp_515_;
}
v___jp_511_:
{
uint8_t v___x_513_; 
v___x_513_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_t_u2081_509_);
if (v___x_513_ == 0)
{
return v___y_512_;
}
else
{
uint8_t v___x_514_; 
v___x_514_ = lean_expr_eqv(v_t_u2081_509_, v_t_u2082_510_);
return v___x_514_;
}
}
v___jp_515_:
{
if (v___y_516_ == 0)
{
return v___y_516_;
}
else
{
v___y_512_ = v___y_516_;
goto v___jp_511_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_u2081_509_ = stack[0].m_obj;
lean_object* v_t_u2082_510_ = stack[1].m_obj;
uint8_t v_res_520_;
v_res_520_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_t_u2081_509_, v_t_u2082_510_);
stack->m_num = v_res_520_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing___boxed(lean_object* v_t_u2081_521_, lean_object* v_t_u2082_522_){
_start:
{
uint8_t v_res_523_; lean_object* v_r_524_; 
v_res_523_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_t_u2081_521_, v_t_u2082_522_);
lean_dec_ref(v_t_u2082_522_);
lean_dec_ref(v_t_u2081_521_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(lean_object* v_x_527_, lean_object* v_xType_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___y_532_; 
if (lean_obj_tag(v_xType_528_) == 4)
{
lean_object* v_declName_571_; 
v_declName_571_ = lean_ctor_get(v_xType_528_, 0);
if (lean_obj_tag(v_declName_571_) == 1)
{
lean_object* v_pre_572_; 
v_pre_572_ = lean_ctor_get(v_declName_571_, 0);
if (lean_obj_tag(v_pre_572_) == 0)
{
lean_object* v_us_573_; lean_object* v_str_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_us_573_ = lean_ctor_get(v_xType_528_, 1);
v_str_574_ = lean_ctor_get(v_declName_571_, 1);
v___x_575_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0));
v___x_576_ = lean_string_dec_eq(v_str_574_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1));
v___x_578_ = lean_string_dec_eq(v_str_574_, v___x_577_);
if (v___x_578_ == 0)
{
v___y_532_ = v_a_529_;
goto v___jp_531_;
}
else
{
if (lean_obj_tag(v_us_573_) == 0)
{
goto v___jp_568_;
}
else
{
v___y_532_ = v_a_529_;
goto v___jp_531_;
}
}
}
else
{
if (lean_obj_tag(v_us_573_) == 0)
{
goto v___jp_568_;
}
else
{
v___y_532_ = v_a_529_;
goto v___jp_531_;
}
}
}
else
{
v___y_532_ = v_a_529_;
goto v___jp_531_;
}
}
else
{
v___y_532_ = v_a_529_;
goto v___jp_531_;
}
}
else
{
v___y_532_ = v_a_529_;
goto v___jp_531_;
}
v___jp_531_:
{
uint8_t v___x_533_; lean_object* v___x_534_; 
v___x_533_ = 1;
v___x_534_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_533_, v_x_527_, v___y_532_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
if (lean_obj_tag(v_a_535_) == 1)
{
lean_object* v_val_536_; 
v_val_536_ = lean_ctor_get(v_a_535_, 0);
switch(lean_obj_tag(v_val_536_))
{
case 0:
{
return v___x_534_;
}
case 9:
{
lean_object* v_args_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_args_537_ = lean_ctor_get(v_val_536_, 1);
v___x_538_ = lean_array_get_size(v_args_537_);
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = lean_nat_dec_eq(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_548_; 
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v___x_534_, 0);
lean_dec(v_unused_549_);
v___x_542_ = v___x_534_;
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
else
{
lean_dec(v___x_534_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_box(0);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
return v___x_534_;
}
}
default: 
{
lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_557_; 
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; 
v_unused_558_ = lean_ctor_get(v___x_534_, 0);
lean_dec(v_unused_558_);
v___x_551_ = v___x_534_;
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
else
{
lean_dec(v___x_534_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_box(0);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
else
{
lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_566_; 
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; 
v_unused_567_ = lean_ctor_get(v___x_534_, 0);
lean_dec(v_unused_567_);
v___x_560_ = v___x_534_;
v_isShared_561_ = v_isSharedCheck_566_;
goto v_resetjp_559_;
}
else
{
lean_dec(v___x_534_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_566_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_562_ = lean_box(0);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_562_);
v___x_564_ = v___x_560_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
else
{
return v___x_534_;
}
}
v___jp_568_:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_box(0);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_527_ = stack[0].m_obj;
lean_object* v_xType_528_ = stack[1].m_obj;
lean_object* v_a_529_ = stack[2].m_obj;
lean_object* v_res_579_;
v_res_579_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_x_527_, v_xType_528_, v_a_529_);
stack->m_obj
 = v_res_579_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___boxed(lean_object* v_x_580_, lean_object* v_xType_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_x_580_, v_xType_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_xType_581_);
lean_dec(v_x_580_);
return v_res_584_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(lean_object* v_x_585_, lean_object* v_xType_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_x_585_, v_xType_586_, v_a_590_);
return v___x_594_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_585_ = stack[0].m_obj;
lean_object* v_xType_586_ = stack[1].m_obj;
lean_object* v_a_587_ = stack[2].m_obj;
lean_object* v_a_588_ = stack[3].m_obj;
lean_object* v_a_589_ = stack[4].m_obj;
lean_object* v_a_590_ = stack[5].m_obj;
lean_object* v_a_591_ = stack[6].m_obj;
lean_object* v_a_592_ = stack[7].m_obj;
lean_object* v_res_595_;
v_res_595_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(v_x_585_, v_xType_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___boxed(lean_object* v_x_596_, lean_object* v_xType_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(v_x_596_, v_xType_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec_ref(v_xType_597_);
lean_dec(v_x_596_);
return v_res_605_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(lean_object* v_fvarId_611_, lean_object* v_fvarIdType_612_, lean_object* v_expectedType_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_expectedType_613_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; lean_object* v___x_623_; 
v___x_622_ = 1;
v___x_623_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_fvarId_611_, v_fvarIdType_612_, v_a_617_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_749_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_749_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_749_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_749_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
if (lean_obj_tag(v_a_624_) == 0)
{
lean_object* v___x_628_; lean_object* v___x_630_; 
lean_dec_ref(v_expectedType_613_);
v___x_628_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_628_, 0, v_fvarIdType_612_);
lean_ctor_set(v___x_628_, 1, v_fvarId_611_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_628_);
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
else
{
lean_object* v_val_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_748_; 
lean_del_object(v___x_626_);
lean_dec(v_fvarId_611_);
v_val_632_ = lean_ctor_get(v_a_624_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v_a_624_);
if (v_isSharedCheck_748_ == 0)
{
v___x_634_ = v_a_624_;
v_isShared_635_ = v_isSharedCheck_748_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_val_632_);
lean_dec(v_a_624_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_748_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
uint8_t v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = 1;
v___x_637_ = lean_box(0);
lean_inc_ref(v_fvarIdType_612_);
v___x_638_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_636_, v___x_637_, v_fvarIdType_612_, v_val_632_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v_fvarId_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
v_fvarId_640_ = lean_ctor_get(v_a_639_, 0);
lean_inc(v_fvarId_640_);
v___x_641_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_641_, 0, v_fvarIdType_612_);
lean_ctor_set(v___x_641_, 1, v_fvarId_640_);
lean_inc_ref(v_expectedType_613_);
v___x_642_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_636_, v___x_637_, v_expectedType_613_, v___x_641_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v_fvarId_644_; lean_object* v___x_646_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v_fvarId_644_ = lean_ctor_get(v_a_643_, 0);
lean_inc(v_fvarId_644_);
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 5);
lean_ctor_set(v___x_634_, 0, v_fvarId_644_);
v___x_646_ = v___x_634_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_fvarId_644_);
v___x_646_ = v_reuseFailAlloc_731_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_currDecl_650_; lean_object* v_nextAuxIdx_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_729_; 
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v_a_643_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v_a_639_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_st_ref_get(v_a_615_);
v_currDecl_650_ = lean_ctor_get(v_a_614_, 0);
v_nextAuxIdx_651_ = lean_ctor_get(v___x_649_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; 
v_unused_730_ = lean_ctor_get(v___x_649_, 0);
lean_dec(v_unused_730_);
v___x_653_ = v___x_649_;
v_isShared_654_ = v_isSharedCheck_729_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_nextAuxIdx_651_);
lean_dec(v___x_649_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_729_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_655_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__1));
v___x_656_ = lean_name_append_index_after(v___x_655_, v_nextAuxIdx_651_);
lean_inc(v_currDecl_650_);
v___x_657_ = l_Lean_Name_append(v_currDecl_650_, v___x_656_);
v___x_658_ = lean_box(0);
v___x_659_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__2));
lean_inc(v___x_657_);
v___x_660_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_660_, 0, v___x_657_);
lean_ctor_set(v___x_660_, 1, v___x_658_);
lean_ctor_set(v___x_660_, 2, v_expectedType_613_);
lean_ctor_set(v___x_660_, 3, v___x_659_);
lean_ctor_set_uint8(v___x_660_, sizeof(void*)*4, v___x_622_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_648_);
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_663_, 0, v___x_660_);
lean_ctor_set(v___x_663_, 1, v___x_661_);
lean_ctor_set(v___x_663_, 2, v___x_662_);
lean_ctor_set_uint8(v___x_663_, sizeof(void*)*3, v___x_621_);
lean_inc_ref(v___x_663_);
v___x_664_ = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(v___x_636_, v___x_663_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_664_, 1);
if (lean_obj_tag(v_a_665_) == 0)
{
lean_object* v___x_666_; lean_object* v_auxDecls_667_; lean_object* v_nextAuxIdx_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_699_; 
v___x_666_ = lean_st_ref_take(v_a_615_);
v_auxDecls_667_ = lean_ctor_get(v___x_666_, 0);
v_nextAuxIdx_668_ = lean_ctor_get(v___x_666_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_699_ == 0)
{
v___x_670_ = v___x_666_;
v_isShared_671_ = v_isSharedCheck_699_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_nextAuxIdx_668_);
lean_inc(v_auxDecls_667_);
lean_dec(v___x_666_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_699_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
lean_inc_ref(v___x_663_);
v___x_672_ = lean_array_push(v_auxDecls_667_, v___x_663_);
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_add(v_nextAuxIdx_668_, v___x_673_);
lean_dec(v_nextAuxIdx_668_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_674_);
lean_ctor_set(v___x_670_, 0, v___x_672_);
v___x_676_ = v___x_670_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_674_);
v___x_676_ = v_reuseFailAlloc_698_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_st_ref_put(v_a_615_, v___x_676_);
v___x_678_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v___x_663_, v_a_619_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_688_; 
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v___x_678_, 0);
lean_dec(v_unused_689_);
v___x_680_ = v___x_678_;
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
else
{
lean_dec(v___x_678_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 9);
lean_ctor_set(v___x_653_, 1, v___x_659_);
lean_ctor_set(v___x_653_, 0, v___x_657_);
v___x_683_ = v___x_653_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_659_);
v___x_683_ = v_reuseFailAlloc_687_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_685_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_683_);
v___x_685_ = v___x_680_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec(v___x_657_);
lean_del_object(v___x_653_);
v_a_690_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_678_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_678_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
}
else
{
lean_object* v_declName_700_; lean_object* v___x_701_; 
lean_dec(v___x_657_);
v_declName_700_ = lean_ctor_get(v_a_665_, 0);
lean_inc(v_declName_700_);
lean_dec_ref_known(v_a_665_, 1);
v___x_701_ = l_Lean_Compiler_LCNF_eraseDecl(v___x_636_, v___x_663_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_711_; 
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; 
v_unused_712_ = lean_ctor_get(v___x_701_, 0);
lean_dec(v_unused_712_);
v___x_703_ = v___x_701_;
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
else
{
lean_dec(v___x_701_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 9);
lean_ctor_set(v___x_653_, 1, v___x_659_);
lean_ctor_set(v___x_653_, 0, v_declName_700_);
v___x_706_ = v___x_653_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_declName_700_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_659_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_706_);
v___x_708_ = v___x_703_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v_declName_700_);
lean_del_object(v___x_653_);
v_a_713_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_701_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_701_);
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
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref_known(v___x_663_, 3);
lean_dec(v___x_657_);
lean_del_object(v___x_653_);
v_a_721_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_664_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_664_);
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
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_a_639_);
lean_del_object(v___x_634_);
lean_dec_ref(v_expectedType_613_);
v_a_732_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_642_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_642_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_del_object(v___x_634_);
lean_dec_ref(v_expectedType_613_);
lean_dec_ref(v_fvarIdType_612_);
v_a_740_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_638_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_638_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref(v_expectedType_613_);
lean_dec_ref(v_fvarIdType_612_);
lean_dec(v_fvarId_611_);
v_a_750_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_623_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_623_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec_ref(v_expectedType_613_);
lean_dec_ref(v_fvarIdType_612_);
v___x_758_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_758_, 0, v_fvarId_611_);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_611_ = stack[0].m_obj;
lean_object* v_fvarIdType_612_ = stack[1].m_obj;
lean_object* v_expectedType_613_ = stack[2].m_obj;
lean_object* v_a_614_ = stack[3].m_obj;
lean_object* v_a_615_ = stack[4].m_obj;
lean_object* v_a_616_ = stack[5].m_obj;
lean_object* v_a_617_ = stack[6].m_obj;
lean_object* v_a_618_ = stack[7].m_obj;
lean_object* v_a_619_ = stack[8].m_obj;
lean_object* v_res_760_;
v_res_760_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_611_, v_fvarIdType_612_, v_expectedType_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
stack->m_obj
 = v_res_760_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___boxed(lean_object* v_fvarId_761_, lean_object* v_fvarIdType_762_, lean_object* v_expectedType_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_761_, v_fvarIdType_762_, v_expectedType_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
return v_res_771_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(lean_object* v_fvarId_772_, lean_object* v_expectedType_773_, lean_object* v_k_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_782_; 
lean_inc(v_fvarId_772_);
v___x_782_ = l_Lean_Compiler_LCNF_getType(v_fvarId_772_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; uint8_t v___x_784_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
v___x_784_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_783_, v_expectedType_773_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_inc_ref(v_expectedType_773_);
v___x_785_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_772_, v_a_783_, v_expectedType_773_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v___x_787_ = 1;
v___x_788_ = lean_box(0);
v___x_789_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_787_, v___x_788_, v_expectedType_773_, v_a_786_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v_fvarId_791_; lean_object* v___x_792_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v_fvarId_791_ = lean_ctor_get(v_a_790_, 0);
lean_inc(v_a_780_);
lean_inc_ref(v_a_779_);
lean_inc(v_a_778_);
lean_inc_ref(v_a_777_);
lean_inc(v_a_776_);
lean_inc_ref(v_a_775_);
lean_inc(v_fvarId_791_);
v___x_792_ = lean_apply_8(v_k_774_, v_fvarId_791_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, lean_box(0));
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_801_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_a_790_);
lean_ctor_set(v___x_797_, 1, v_a_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
else
{
lean_dec(v_a_790_);
return v___x_792_;
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v_k_774_);
v_a_802_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_789_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_789_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v_k_774_);
lean_dec_ref(v_expectedType_773_);
v_a_810_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_785_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_785_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v___x_818_; 
lean_dec(v_a_783_);
lean_dec_ref(v_expectedType_773_);
lean_inc(v_a_780_);
lean_inc_ref(v_a_779_);
lean_inc(v_a_778_);
lean_inc_ref(v_a_777_);
lean_inc(v_a_776_);
lean_inc_ref(v_a_775_);
v___x_818_ = lean_apply_8(v_k_774_, v_fvarId_772_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, lean_box(0));
return v___x_818_;
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_k_774_);
lean_dec_ref(v_expectedType_773_);
lean_dec(v_fvarId_772_);
v_a_819_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_782_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_782_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_772_ = stack[0].m_obj;
lean_object* v_expectedType_773_ = stack[1].m_obj;
lean_object* v_k_774_ = stack[2].m_obj;
lean_object* v_a_775_ = stack[3].m_obj;
lean_object* v_a_776_ = stack[4].m_obj;
lean_object* v_a_777_ = stack[5].m_obj;
lean_object* v_a_778_ = stack[6].m_obj;
lean_object* v_a_779_ = stack[7].m_obj;
lean_object* v_a_780_ = stack[8].m_obj;
lean_object* v_res_827_;
v_res_827_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(v_fvarId_772_, v_expectedType_773_, v_k_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
stack->m_obj
 = v_res_827_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded___boxed(lean_object* v_fvarId_828_, lean_object* v_expectedType_829_, lean_object* v_k_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(v_fvarId_828_, v_expectedType_829_, v_k_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
return v_res_838_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(lean_object* v_arg_839_, lean_object* v_k_840_, lean_object* v_x_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(v_arg_839_, v_x_841_);
lean_inc(v___y_847_);
lean_inc_ref(v___y_846_);
lean_inc(v___y_845_);
lean_inc_ref(v___y_844_);
lean_inc(v___y_843_);
lean_inc_ref(v___y_842_);
v___x_850_ = lean_apply_8(v_k_840_, v___x_849_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, lean_box(0));
return v___x_850_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_839_ = stack[0].m_obj;
lean_object* v_k_840_ = stack[1].m_obj;
lean_object* v_x_841_ = stack[2].m_obj;
lean_object* v___y_842_ = stack[3].m_obj;
lean_object* v___y_843_ = stack[4].m_obj;
lean_object* v___y_844_ = stack[5].m_obj;
lean_object* v___y_845_ = stack[6].m_obj;
lean_object* v___y_846_ = stack[7].m_obj;
lean_object* v___y_847_ = stack[8].m_obj;
lean_object* v_res_851_;
v_res_851_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_839_, v_k_840_, v_x_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0___boxed(lean_object* v_arg_852_, lean_object* v_k_853_, lean_object* v_x_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_852_, v_k_853_, v_x_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_862_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(lean_object* v_arg_863_, lean_object* v_expectedType_864_, lean_object* v_k_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
if (lean_obj_tag(v_arg_863_) == 0)
{
lean_object* v___x_873_; 
lean_dec_ref(v_expectedType_864_);
lean_inc(v_a_871_);
lean_inc_ref(v_a_870_);
lean_inc(v_a_869_);
lean_inc_ref(v_a_868_);
lean_inc(v_a_867_);
lean_inc_ref(v_a_866_);
v___x_873_ = lean_apply_8(v_k_865_, v_arg_863_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, lean_box(0));
return v___x_873_;
}
else
{
lean_object* v_fvarId_874_; lean_object* v___x_875_; 
v_fvarId_874_ = lean_ctor_get(v_arg_863_, 0);
lean_inc(v_fvarId_874_);
v___x_875_ = l_Lean_Compiler_LCNF_getType(v_fvarId_874_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; uint8_t v___x_877_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
v___x_877_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_876_, v_expectedType_864_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
lean_inc_ref(v_expectedType_864_);
lean_inc(v_fvarId_874_);
v___x_878_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_874_, v_a_876_, v_expectedType_864_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
v___x_880_ = 1;
v___x_881_ = lean_box(0);
v___x_882_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_880_, v___x_881_, v_expectedType_864_, v_a_879_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v_fvarId_884_; lean_object* v___x_885_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v_fvarId_884_ = lean_ctor_get(v_a_883_, 0);
lean_inc(v_fvarId_884_);
v___x_885_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_863_, v_k_865_, v_fvarId_884_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_894_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_894_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v_a_883_);
lean_ctor_set(v___x_890_, 1, v_a_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
else
{
lean_dec(v_a_883_);
return v___x_885_;
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref_known(v_arg_863_, 1);
lean_dec_ref(v_k_865_);
v_a_895_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_882_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_882_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref_known(v_arg_863_, 1);
lean_dec_ref(v_k_865_);
lean_dec_ref(v_expectedType_864_);
v_a_903_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_878_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_878_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v___x_911_; 
lean_inc(v_fvarId_874_);
lean_dec(v_a_876_);
lean_dec_ref(v_expectedType_864_);
v___x_911_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_863_, v_k_865_, v_fvarId_874_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
return v___x_911_;
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref_known(v_arg_863_, 1);
lean_dec_ref(v_k_865_);
lean_dec_ref(v_expectedType_864_);
v_a_912_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_875_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_875_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_863_ = stack[0].m_obj;
lean_object* v_expectedType_864_ = stack[1].m_obj;
lean_object* v_k_865_ = stack[2].m_obj;
lean_object* v_a_866_ = stack[3].m_obj;
lean_object* v_a_867_ = stack[4].m_obj;
lean_object* v_a_868_ = stack[5].m_obj;
lean_object* v_a_869_ = stack[6].m_obj;
lean_object* v_a_870_ = stack[7].m_obj;
lean_object* v_a_871_ = stack[8].m_obj;
lean_object* v_res_920_;
v_res_920_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(v_arg_863_, v_expectedType_864_, v_k_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
stack->m_obj
 = v_res_920_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___boxed(lean_object* v_arg_921_, lean_object* v_expectedType_922_, lean_object* v_k_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(v_arg_921_, v_expectedType_922_, v_k_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
return v_res_931_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(lean_object* v_upperBound_932_, lean_object* v_args_933_, lean_object* v_typeFromIdx_934_, lean_object* v_a_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_a_945_; uint8_t v___x_949_; 
v___x_949_ = lean_nat_dec_lt(v_a_935_, v_upperBound_932_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
lean_dec(v_a_935_);
lean_dec_ref(v_typeFromIdx_934_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_b_936_);
return v___x_950_;
}
else
{
lean_object* v_fst_951_; lean_object* v_snd_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_1015_; 
v_fst_951_ = lean_ctor_get(v_b_936_, 0);
v_snd_952_ = lean_ctor_get(v_b_936_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_b_936_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_954_ = v_b_936_;
v_isShared_955_ = v_isSharedCheck_1015_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_snd_952_);
lean_inc(v_fst_951_);
lean_dec(v_b_936_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_1015_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; 
v___x_956_ = lean_array_fget(v_args_933_, v_a_935_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = lean_array_push(v_fst_951_, v___x_956_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_957_);
v___x_959_ = v___x_954_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_snd_952_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
v_a_945_ = v___x_959_;
goto v___jp_944_;
}
}
else
{
lean_object* v_fvarId_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_fvarId_961_ = lean_ctor_get(v___x_956_, 0);
lean_inc_ref(v_typeFromIdx_934_);
lean_inc(v_a_935_);
v___x_962_ = lean_apply_1(v_typeFromIdx_934_, v_a_935_);
lean_inc(v_fvarId_961_);
v___x_963_ = l_Lean_Compiler_LCNF_getType(v_fvarId_961_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; uint8_t v___x_965_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
v___x_965_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_964_, v___x_962_);
if (v___x_965_ == 0)
{
lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_1001_; 
lean_inc(v_fvarId_961_);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1001_ == 0)
{
lean_object* v_unused_1002_; 
v_unused_1002_ = lean_ctor_get(v___x_956_, 0);
lean_dec(v_unused_1002_);
v___x_967_ = v___x_956_;
v_isShared_968_ = v_isSharedCheck_1001_;
goto v_resetjp_966_;
}
else
{
lean_dec(v___x_956_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_1001_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; 
lean_inc_ref(v___x_962_);
v___x_969_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_961_, v_a_964_, v___x_962_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = 1;
v___x_972_ = lean_box(0);
v___x_973_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_971_, v___x_972_, v___x_962_, v_a_970_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v_fvarId_975_; lean_object* v___x_977_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v_fvarId_975_ = lean_ctor_get(v_a_974_, 0);
lean_inc(v_fvarId_975_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v_fvarId_975_);
v___x_977_ = v___x_967_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_fvarId_975_);
v___x_977_ = v_reuseFailAlloc_984_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_978_ = lean_array_push(v_fst_951_, v___x_977_);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v_a_974_);
v___x_980_ = lean_array_push(v_snd_952_, v___x_979_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v___x_980_);
lean_ctor_set(v___x_954_, 0, v___x_978_);
v___x_982_ = v___x_954_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
v_a_945_ = v___x_982_;
goto v___jp_944_;
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_del_object(v___x_967_);
lean_del_object(v___x_954_);
lean_dec(v_snd_952_);
lean_dec(v_fst_951_);
lean_dec(v_a_935_);
lean_dec_ref(v_typeFromIdx_934_);
v_a_985_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_973_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_973_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_del_object(v___x_967_);
lean_dec_ref(v___x_962_);
lean_del_object(v___x_954_);
lean_dec(v_snd_952_);
lean_dec(v_fst_951_);
lean_dec(v_a_935_);
lean_dec_ref(v_typeFromIdx_934_);
v_a_993_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_969_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_969_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec(v_a_964_);
lean_dec_ref(v___x_962_);
v___x_1003_ = lean_array_push(v_fst_951_, v___x_956_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_1003_);
v___x_1005_ = v___x_954_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_snd_952_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
v_a_945_ = v___x_1005_;
goto v___jp_944_;
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v___x_962_);
lean_dec_ref_known(v___x_956_, 1);
lean_del_object(v___x_954_);
lean_dec(v_snd_952_);
lean_dec(v_fst_951_);
lean_dec(v_a_935_);
lean_dec_ref(v_typeFromIdx_934_);
v_a_1007_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_963_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_963_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
}
v___jp_944_:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_unsigned_to_nat(1u);
v___x_947_ = lean_nat_add(v_a_935_, v___x_946_);
lean_dec(v_a_935_);
v_a_935_ = v___x_947_;
v_b_936_ = v_a_945_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_932_ = stack[0].m_obj;
lean_object* v_args_933_ = stack[1].m_obj;
lean_object* v_typeFromIdx_934_ = stack[2].m_obj;
lean_object* v_a_935_ = stack[3].m_obj;
lean_object* v_b_936_ = stack[4].m_obj;
lean_object* v___y_937_ = stack[5].m_obj;
lean_object* v___y_938_ = stack[6].m_obj;
lean_object* v___y_939_ = stack[7].m_obj;
lean_object* v___y_940_ = stack[8].m_obj;
lean_object* v___y_941_ = stack[9].m_obj;
lean_object* v___y_942_ = stack[10].m_obj;
lean_object* v_res_1016_;
v_res_1016_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v_upperBound_932_, v_args_933_, v_typeFromIdx_934_, v_a_935_, v_b_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
stack->m_obj
 = v_res_1016_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg___boxed(lean_object* v_upperBound_1017_, lean_object* v_args_1018_, lean_object* v_typeFromIdx_1019_, lean_object* v_a_1020_, lean_object* v_b_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v_upperBound_1017_, v_args_1018_, v_typeFromIdx_1019_, v_a_1020_, v_b_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec_ref(v_args_1018_);
lean_dec(v_upperBound_1017_);
return v_res_1029_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(lean_object* v_args_1030_, lean_object* v_typeFromIdx_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1039_; lean_object* v_newArgs_1040_; lean_object* v___x_1041_; lean_object* v_casters_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1039_ = lean_array_get_size(v_args_1030_);
v_newArgs_1040_ = lean_mk_empty_array_with_capacity(v___x_1039_);
v___x_1041_ = lean_unsigned_to_nat(0u);
v_casters_1042_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0));
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_newArgs_1040_);
lean_ctor_set(v___x_1043_, 1, v_casters_1042_);
v___x_1044_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v___x_1039_, v_args_1030_, v_typeFromIdx_1031_, v___x_1041_, v___x_1043_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1061_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1061_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1061_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v_fst_1049_; lean_object* v_snd_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1060_; 
v_fst_1049_ = lean_ctor_get(v_a_1045_, 0);
v_snd_1050_ = lean_ctor_get(v_a_1045_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_a_1045_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1052_ = v_a_1045_;
v_isShared_1053_ = v_isSharedCheck_1060_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_snd_1050_);
lean_inc(v_fst_1049_);
lean_dec(v_a_1045_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1060_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_fst_1049_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_snd_1050_);
v___x_1055_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1055_);
v___x_1057_ = v___x_1047_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
else
{
return v___x_1044_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_1030_ = stack[0].m_obj;
lean_object* v_typeFromIdx_1031_ = stack[1].m_obj;
lean_object* v_a_1032_ = stack[2].m_obj;
lean_object* v_a_1033_ = stack[3].m_obj;
lean_object* v_a_1034_ = stack[4].m_obj;
lean_object* v_a_1035_ = stack[5].m_obj;
lean_object* v_a_1036_ = stack[6].m_obj;
lean_object* v_a_1037_ = stack[7].m_obj;
lean_object* v_res_1062_;
v_res_1062_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1030_, v_typeFromIdx_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
stack->m_obj
 = v_res_1062_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux___boxed(lean_object* v_args_1063_, lean_object* v_typeFromIdx_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1063_, v_typeFromIdx_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec_ref(v_args_1063_);
return v_res_1072_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(lean_object* v_upperBound_1073_, lean_object* v_args_1074_, lean_object* v_typeFromIdx_1075_, lean_object* v_inst_1076_, lean_object* v_R_1077_, lean_object* v_a_1078_, lean_object* v_b_1079_, lean_object* v_c_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v_upperBound_1073_, v_args_1074_, v_typeFromIdx_1075_, v_a_1078_, v_b_1079_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
return v___x_1088_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1073_ = stack[0].m_obj;
lean_object* v_args_1074_ = stack[1].m_obj;
lean_object* v_typeFromIdx_1075_ = stack[2].m_obj;
lean_object* v_a_1078_ = stack[5].m_obj;
lean_object* v_b_1079_ = stack[6].m_obj;
lean_object* v___y_1081_ = stack[8].m_obj;
lean_object* v___y_1082_ = stack[9].m_obj;
lean_object* v___y_1083_ = stack[10].m_obj;
lean_object* v___y_1084_ = stack[11].m_obj;
lean_object* v___y_1085_ = stack[12].m_obj;
lean_object* v___y_1086_ = stack[13].m_obj;
lean_object* v_res_1089_;
v_res_1089_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(v_upperBound_1073_, v_args_1074_, v_typeFromIdx_1075_, lean_box(0), lean_box(0), v_a_1078_, v_b_1079_, lean_box(0), v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
stack->m_obj
 = v_res_1089_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___boxed(lean_object* v_upperBound_1090_, lean_object* v_args_1091_, lean_object* v_typeFromIdx_1092_, lean_object* v_inst_1093_, lean_object* v_R_1094_, lean_object* v_a_1095_, lean_object* v_b_1096_, lean_object* v_c_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(v_upperBound_1090_, v_args_1091_, v_typeFromIdx_1092_, v_inst_1093_, v_R_1094_, v_a_1095_, v_b_1096_, v_c_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec_ref(v_args_1091_);
lean_dec(v_upperBound_1090_);
return v_res_1105_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(lean_object* v_ps_1107_, lean_object* v_i_1108_){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v_type_1111_; 
v___x_1109_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0);
v___x_1110_ = lean_array_get_borrowed(v___x_1109_, v_ps_1107_, v_i_1108_);
v_type_1111_ = lean_ctor_get(v___x_1110_, 2);
lean_inc_ref(v_type_1111_);
return v_type_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed(lean_object* v_ps_1112_, lean_object* v_i_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(v_ps_1112_, v_i_1113_);
lean_dec(v_i_1113_);
lean_dec_ref(v_ps_1112_);
return v_res_1114_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(lean_object* v_args_1115_, lean_object* v_ps_1116_, lean_object* v_k_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v___f_1125_; lean_object* v___x_1126_; 
v___f_1125_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1125_, 0, v_ps_1116_);
v___x_1126_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1115_, v___f_1125_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v_fst_1128_; lean_object* v_snd_1129_; lean_object* v___x_1130_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1126_, 1);
v_fst_1128_ = lean_ctor_get(v_a_1127_, 0);
lean_inc(v_fst_1128_);
v_snd_1129_ = lean_ctor_get(v_a_1127_, 1);
lean_inc(v_snd_1129_);
lean_dec(v_a_1127_);
lean_inc(v_a_1123_);
lean_inc_ref(v_a_1122_);
lean_inc(v_a_1121_);
lean_inc_ref(v_a_1120_);
lean_inc(v_a_1119_);
lean_inc_ref(v_a_1118_);
v___x_1130_ = lean_apply_8(v_k_1117_, v_fst_1128_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, lean_box(0));
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1139_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1135_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_1129_, v_a_1131_);
lean_dec(v_snd_1129_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1135_);
v___x_1137_ = v___x_1133_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
else
{
lean_dec(v_snd_1129_);
return v___x_1130_;
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v_k_1117_);
v_a_1140_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1126_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1126_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_1115_ = stack[0].m_obj;
lean_object* v_ps_1116_ = stack[1].m_obj;
lean_object* v_k_1117_ = stack[2].m_obj;
lean_object* v_a_1118_ = stack[3].m_obj;
lean_object* v_a_1119_ = stack[4].m_obj;
lean_object* v_a_1120_ = stack[5].m_obj;
lean_object* v_a_1121_ = stack[6].m_obj;
lean_object* v_a_1122_ = stack[7].m_obj;
lean_object* v_a_1123_ = stack[8].m_obj;
lean_object* v_res_1148_;
v_res_1148_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(v_args_1115_, v_ps_1116_, v_k_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
stack->m_obj
 = v_res_1148_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___boxed(lean_object* v_args_1149_, lean_object* v_ps_1150_, lean_object* v_k_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(v_args_1149_, v_ps_1150_, v_k_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec_ref(v_args_1149_);
return v_res_1159_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_box(0);
v___x_1164_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1));
v___x_1165_ = l_Lean_Expr_const___override(v___x_1164_, v___x_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(lean_object* v_x_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___boxed(lean_object* v_x_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(v_x_1168_);
lean_dec(v_x_1168_);
return v_res_1169_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(lean_object* v_args_1171_, lean_object* v_k_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___f_1180_; lean_object* v___x_1181_; 
v___f_1180_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0));
v___x_1181_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1171_, v___f_1180_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v_fst_1183_; lean_object* v_snd_1184_; lean_object* v___x_1185_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v_fst_1183_ = lean_ctor_get(v_a_1182_, 0);
lean_inc(v_fst_1183_);
v_snd_1184_ = lean_ctor_get(v_a_1182_, 1);
lean_inc(v_snd_1184_);
lean_dec(v_a_1182_);
lean_inc(v_a_1178_);
lean_inc_ref(v_a_1177_);
lean_inc(v_a_1176_);
lean_inc_ref(v_a_1175_);
lean_inc(v_a_1174_);
lean_inc_ref(v_a_1173_);
v___x_1185_ = lean_apply_8(v_k_1172_, v_fst_1183_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, lean_box(0));
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1194_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_1184_, v_a_1186_);
lean_dec(v_snd_1184_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
else
{
lean_dec(v_snd_1184_);
return v___x_1185_;
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec_ref(v_k_1172_);
v_a_1195_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1181_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1181_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_1171_ = stack[0].m_obj;
lean_object* v_k_1172_ = stack[1].m_obj;
lean_object* v_a_1173_ = stack[2].m_obj;
lean_object* v_a_1174_ = stack[3].m_obj;
lean_object* v_a_1175_ = stack[4].m_obj;
lean_object* v_a_1176_ = stack[5].m_obj;
lean_object* v_a_1177_ = stack[6].m_obj;
lean_object* v_a_1178_ = stack[7].m_obj;
lean_object* v_res_1203_;
v_res_1203_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(v_args_1171_, v_k_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
stack->m_obj
 = v_res_1203_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___boxed(lean_object* v_args_1204_, lean_object* v_k_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(v_args_1204_, v_k_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec_ref(v_args_1204_);
return v_res_1213_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(lean_object* v_msg_1215_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
v___x_1217_ = lean_panic_fn_borrowed(v___x_1216_, v_msg_1215_);
return v___x_1217_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1222_ = lean_unsigned_to_nat(9u);
v___x_1223_ = lean_unsigned_to_nat(625u);
v___x_1224_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1));
v___x_1225_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0));
v___x_1226_ = l_mkPanicMessageWithDecl(v___x_1225_, v___x_1224_, v___x_1223_, v___x_1222_, v___x_1221_);
return v___x_1226_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(lean_object* v_code_1227_, lean_object* v_decl_1228_, lean_object* v_k_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_type_1235_; lean_object* v_value_1236_; uint8_t v___x_1237_; 
v_type_1235_ = lean_ctor_get(v_decl_1228_, 2);
v_value_1236_ = lean_ctor_get(v_decl_1228_, 3);
v___x_1237_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_1235_);
if (v___x_1237_ == 0)
{
if (lean_obj_tag(v_code_1227_) == 0)
{
lean_object* v_decl_1238_; lean_object* v_k_1239_; size_t v___x_1240_; size_t v___x_1241_; uint8_t v___x_1242_; 
v_decl_1238_ = lean_ctor_get(v_code_1227_, 0);
v_k_1239_ = lean_ctor_get(v_code_1227_, 1);
v___x_1240_ = lean_ptr_addr(v_k_1239_);
v___x_1241_ = lean_ptr_addr(v_k_1229_);
v___x_1242_ = lean_usize_dec_eq(v___x_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1250_; 
v_isSharedCheck_1250_ = !lean_is_exclusive(v_code_1227_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; lean_object* v_unused_1252_; 
v_unused_1251_ = lean_ctor_get(v_code_1227_, 1);
lean_dec(v_unused_1251_);
v_unused_1252_ = lean_ctor_get(v_code_1227_, 0);
lean_dec(v_unused_1252_);
v___x_1244_ = v_code_1227_;
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
else
{
lean_dec(v_code_1227_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v_k_1229_);
lean_ctor_set(v___x_1244_, 0, v_decl_1228_);
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_decl_1228_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_k_1229_);
v___x_1247_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
return v___x_1248_;
}
}
}
else
{
size_t v___x_1253_; size_t v___x_1254_; uint8_t v___x_1255_; 
v___x_1253_ = lean_ptr_addr(v_decl_1238_);
v___x_1254_ = lean_ptr_addr(v_decl_1228_);
v___x_1255_ = lean_usize_dec_eq(v___x_1253_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1263_; 
v_isSharedCheck_1263_ = !lean_is_exclusive(v_code_1227_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; lean_object* v_unused_1265_; 
v_unused_1264_ = lean_ctor_get(v_code_1227_, 1);
lean_dec(v_unused_1264_);
v_unused_1265_ = lean_ctor_get(v_code_1227_, 0);
lean_dec(v_unused_1265_);
v___x_1257_ = v_code_1227_;
v_isShared_1258_ = v_isSharedCheck_1263_;
goto v_resetjp_1256_;
}
else
{
lean_dec(v_code_1227_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1263_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_k_1229_);
lean_ctor_set(v___x_1257_, 0, v_decl_1228_);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_decl_1228_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_k_1229_);
v___x_1260_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
}
}
else
{
lean_object* v___x_1266_; 
lean_dec_ref(v_k_1229_);
lean_dec_ref(v_decl_1228_);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v_code_1227_);
return v___x_1266_;
}
}
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec_ref(v_k_1229_);
lean_dec_ref(v_decl_1228_);
lean_dec_ref(v_code_1227_);
v___x_1267_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_1268_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_1267_);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
}
else
{
uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec_ref(v_code_1227_);
v___x_1270_ = 1;
v___x_1271_ = lean_box(0);
v___x_1272_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
lean_inc(v_value_1236_);
v___x_1273_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1270_, v___x_1271_, v___x_1272_, v_value_1236_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v_fvarId_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___x_1273_, 1);
v_fvarId_1275_ = lean_ctor_get(v_a_1274_, 0);
lean_inc(v_fvarId_1275_);
v___x_1276_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_1276_, 0, v_fvarId_1275_);
v___x_1277_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1270_, v_decl_1228_, v___x_1276_, v_a_1231_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1287_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1287_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1287_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v_a_1278_);
lean_ctor_set(v___x_1282_, 1, v_k_1229_);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_a_1274_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1283_);
v___x_1285_ = v___x_1280_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_a_1274_);
lean_dec_ref(v_k_1229_);
v_a_1288_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1277_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1277_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_k_1229_);
lean_dec_ref(v_decl_1228_);
v_a_1296_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1273_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1273_);
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
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_1227_ = stack[0].m_obj;
lean_object* v_decl_1228_ = stack[1].m_obj;
lean_object* v_k_1229_ = stack[2].m_obj;
lean_object* v_a_1230_ = stack[3].m_obj;
lean_object* v_a_1231_ = stack[4].m_obj;
lean_object* v_a_1232_ = stack[5].m_obj;
lean_object* v_a_1233_ = stack[6].m_obj;
lean_object* v_res_1304_;
v_res_1304_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1227_, v_decl_1228_, v_k_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
stack->m_obj
 = v_res_1304_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___boxed(lean_object* v_code_1305_, lean_object* v_decl_1306_, lean_object* v_k_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1305_, v_decl_1306_, v_k_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
return v_res_1313_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(lean_object* v_code_1314_, lean_object* v_decl_1315_, lean_object* v_k_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1314_, v_decl_1315_, v_k_1316_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
return v___x_1324_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_1314_ = stack[0].m_obj;
lean_object* v_decl_1315_ = stack[1].m_obj;
lean_object* v_k_1316_ = stack[2].m_obj;
lean_object* v_a_1317_ = stack[3].m_obj;
lean_object* v_a_1318_ = stack[4].m_obj;
lean_object* v_a_1319_ = stack[5].m_obj;
lean_object* v_a_1320_ = stack[6].m_obj;
lean_object* v_a_1321_ = stack[7].m_obj;
lean_object* v_a_1322_ = stack[8].m_obj;
lean_object* v_res_1325_;
v_res_1325_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(v_code_1314_, v_decl_1315_, v_k_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
stack->m_obj
 = v_res_1325_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___boxed(lean_object* v_code_1326_, lean_object* v_decl_1327_, lean_object* v_k_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(v_code_1326_, v_decl_1327_, v_k_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
return v_res_1336_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(lean_object* v_code_1337_, lean_object* v_decl_1338_, lean_object* v_expType_1339_, lean_object* v_k_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_type_1348_; lean_object* v_value_1349_; uint8_t v___x_1350_; 
v_type_1348_ = lean_ctor_get(v_decl_1338_, 2);
v_value_1349_ = lean_ctor_get(v_decl_1338_, 3);
v___x_1350_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_type_1348_, v_expType_1339_);
if (v___x_1350_ == 0)
{
lean_object* v_boxedTy_1351_; uint8_t v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec_ref(v_code_1337_);
v_boxedTy_1351_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_1348_);
v___x_1352_ = 1;
v___x_1353_ = lean_box(0);
lean_inc(v_value_1349_);
v___x_1354_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1352_, v___x_1353_, v_boxedTy_1351_, v_value_1349_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v_fvarId_1356_; lean_object* v_type_1357_; lean_object* v___x_1358_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v_fvarId_1356_ = lean_ctor_get(v_a_1355_, 0);
v_type_1357_ = lean_ctor_get(v_a_1355_, 2);
lean_inc_ref(v_type_1348_);
lean_inc_ref(v_type_1357_);
lean_inc(v_fvarId_1356_);
v___x_1358_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_1356_, v_type_1357_, v_type_1348_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1360_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1358_, 1);
v___x_1360_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1352_, v_decl_1338_, v_a_1359_, v_a_1344_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1370_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1370_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1370_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_a_1361_);
lean_ctor_set(v___x_1365_, 1, v_k_1340_);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_a_1355_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1366_);
v___x_1368_ = v___x_1363_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_a_1355_);
lean_dec_ref(v_k_1340_);
v_a_1371_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1360_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1360_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_a_1355_);
lean_dec_ref(v_k_1340_);
lean_dec_ref(v_decl_1338_);
v_a_1379_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1358_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1358_);
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
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec_ref(v_k_1340_);
lean_dec_ref(v_decl_1338_);
v_a_1387_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1354_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1354_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
if (lean_obj_tag(v_code_1337_) == 0)
{
lean_object* v_decl_1395_; lean_object* v_k_1396_; size_t v___x_1397_; size_t v___x_1398_; uint8_t v___x_1399_; 
v_decl_1395_ = lean_ctor_get(v_code_1337_, 0);
v_k_1396_ = lean_ctor_get(v_code_1337_, 1);
v___x_1397_ = lean_ptr_addr(v_k_1396_);
v___x_1398_ = lean_ptr_addr(v_k_1340_);
v___x_1399_ = lean_usize_dec_eq(v___x_1397_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1407_; 
v_isSharedCheck_1407_ = !lean_is_exclusive(v_code_1337_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; lean_object* v_unused_1409_; 
v_unused_1408_ = lean_ctor_get(v_code_1337_, 1);
lean_dec(v_unused_1408_);
v_unused_1409_ = lean_ctor_get(v_code_1337_, 0);
lean_dec(v_unused_1409_);
v___x_1401_ = v_code_1337_;
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
else
{
lean_dec(v_code_1337_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 1, v_k_1340_);
lean_ctor_set(v___x_1401_, 0, v_decl_1338_);
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_decl_1338_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_k_1340_);
v___x_1404_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
}
}
else
{
size_t v___x_1410_; size_t v___x_1411_; uint8_t v___x_1412_; 
v___x_1410_ = lean_ptr_addr(v_decl_1395_);
v___x_1411_ = lean_ptr_addr(v_decl_1338_);
v___x_1412_ = lean_usize_dec_eq(v___x_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1420_; 
v_isSharedCheck_1420_ = !lean_is_exclusive(v_code_1337_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; lean_object* v_unused_1422_; 
v_unused_1421_ = lean_ctor_get(v_code_1337_, 1);
lean_dec(v_unused_1421_);
v_unused_1422_ = lean_ctor_get(v_code_1337_, 0);
lean_dec(v_unused_1422_);
v___x_1414_ = v_code_1337_;
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
else
{
lean_dec(v_code_1337_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 1, v_k_1340_);
lean_ctor_set(v___x_1414_, 0, v_decl_1338_);
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_decl_1338_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_k_1340_);
v___x_1417_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
}
}
else
{
lean_object* v___x_1423_; 
lean_dec_ref(v_k_1340_);
lean_dec_ref(v_decl_1338_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_code_1337_);
return v___x_1423_;
}
}
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec_ref(v_k_1340_);
lean_dec_ref(v_decl_1338_);
lean_dec_ref(v_code_1337_);
v___x_1424_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_1425_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_1424_);
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_1337_ = stack[0].m_obj;
lean_object* v_decl_1338_ = stack[1].m_obj;
lean_object* v_expType_1339_ = stack[2].m_obj;
lean_object* v_k_1340_ = stack[3].m_obj;
lean_object* v_a_1341_ = stack[4].m_obj;
lean_object* v_a_1342_ = stack[5].m_obj;
lean_object* v_a_1343_ = stack[6].m_obj;
lean_object* v_a_1344_ = stack[7].m_obj;
lean_object* v_a_1345_ = stack[8].m_obj;
lean_object* v_a_1346_ = stack[9].m_obj;
lean_object* v_res_1427_;
v_res_1427_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(v_code_1337_, v_decl_1338_, v_expType_1339_, v_k_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_);
stack->m_obj
 = v_res_1427_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded___boxed(lean_object* v_code_1428_, lean_object* v_decl_1429_, lean_object* v_expType_1430_, lean_object* v_k_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(v_code_1428_, v_decl_1429_, v_expType_1430_, v_k_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
lean_dec(v_a_1433_);
lean_dec_ref(v_a_1432_);
lean_dec_ref(v_expType_1430_);
return v_res_1439_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_instMonadEIO___redArg();
return v___x_1440_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(lean_object* v_msg_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_toApplicative_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1518_; 
v___x_1453_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
v___x_1454_ = l_StateRefT_x27_instMonad___redArg(v___x_1453_);
v_toApplicative_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1518_ == 0)
{
lean_object* v_unused_1519_; 
v_unused_1519_ = lean_ctor_get(v___x_1454_, 1);
lean_dec(v_unused_1519_);
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1518_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_toApplicative_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1518_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v_toFunctor_1459_; lean_object* v_toSeq_1460_; lean_object* v_toSeqLeft_1461_; lean_object* v_toSeqRight_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1516_; 
v_toFunctor_1459_ = lean_ctor_get(v_toApplicative_1455_, 0);
v_toSeq_1460_ = lean_ctor_get(v_toApplicative_1455_, 2);
v_toSeqLeft_1461_ = lean_ctor_get(v_toApplicative_1455_, 3);
v_toSeqRight_1462_ = lean_ctor_get(v_toApplicative_1455_, 4);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_toApplicative_1455_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v_toApplicative_1455_, 1);
lean_dec(v_unused_1517_);
v___x_1464_ = v_toApplicative_1455_;
v_isShared_1465_ = v_isSharedCheck_1516_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_toSeqRight_1462_);
lean_inc(v_toSeqLeft_1461_);
lean_inc(v_toSeq_1460_);
lean_inc(v_toFunctor_1459_);
lean_dec(v_toApplicative_1455_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1516_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___f_1466_; lean_object* v___f_1467_; lean_object* v___f_1468_; lean_object* v___f_1469_; lean_object* v___x_1470_; lean_object* v___f_1471_; lean_object* v___f_1472_; lean_object* v___f_1473_; lean_object* v___x_1475_; 
v___f_1466_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1));
v___f_1467_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1459_);
v___f_1468_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1468_, 0, v_toFunctor_1459_);
v___f_1469_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1469_, 0, v_toFunctor_1459_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___f_1468_);
lean_ctor_set(v___x_1470_, 1, v___f_1469_);
v___f_1471_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1471_, 0, v_toSeqRight_1462_);
v___f_1472_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1472_, 0, v_toSeqLeft_1461_);
v___f_1473_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1473_, 0, v_toSeq_1460_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 4, v___f_1471_);
lean_ctor_set(v___x_1464_, 3, v___f_1472_);
lean_ctor_set(v___x_1464_, 2, v___f_1473_);
lean_ctor_set(v___x_1464_, 1, v___f_1466_);
lean_ctor_set(v___x_1464_, 0, v___x_1470_);
v___x_1475_ = v___x_1464_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v___f_1466_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v___f_1473_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v___f_1472_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v___f_1471_);
v___x_1475_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 1, v___f_1467_);
lean_ctor_set(v___x_1457_, 0, v___x_1475_);
v___x_1477_ = v___x_1457_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___f_1467_);
v___x_1477_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; lean_object* v_toApplicative_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1512_; 
v___x_1478_ = l_StateRefT_x27_instMonad___redArg(v___x_1477_);
v_toApplicative_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v___x_1478_, 1);
lean_dec(v_unused_1513_);
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1512_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_toApplicative_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1512_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v_toFunctor_1483_; lean_object* v_toSeq_1484_; lean_object* v_toSeqLeft_1485_; lean_object* v_toSeqRight_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1510_; 
v_toFunctor_1483_ = lean_ctor_get(v_toApplicative_1479_, 0);
v_toSeq_1484_ = lean_ctor_get(v_toApplicative_1479_, 2);
v_toSeqLeft_1485_ = lean_ctor_get(v_toApplicative_1479_, 3);
v_toSeqRight_1486_ = lean_ctor_get(v_toApplicative_1479_, 4);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_toApplicative_1479_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v_toApplicative_1479_, 1);
lean_dec(v_unused_1511_);
v___x_1488_ = v_toApplicative_1479_;
v_isShared_1489_ = v_isSharedCheck_1510_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_toSeqRight_1486_);
lean_inc(v_toSeqLeft_1485_);
lean_inc(v_toSeq_1484_);
lean_inc(v_toFunctor_1483_);
lean_dec(v_toApplicative_1479_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1510_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___f_1490_; lean_object* v___f_1491_; lean_object* v___f_1492_; lean_object* v___f_1493_; lean_object* v___x_1494_; lean_object* v___f_1495_; lean_object* v___f_1496_; lean_object* v___f_1497_; lean_object* v___x_1499_; 
v___f_1490_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3));
v___f_1491_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1483_);
v___f_1492_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1492_, 0, v_toFunctor_1483_);
v___f_1493_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1493_, 0, v_toFunctor_1483_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___f_1492_);
lean_ctor_set(v___x_1494_, 1, v___f_1493_);
v___f_1495_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1495_, 0, v_toSeqRight_1486_);
v___f_1496_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1496_, 0, v_toSeqLeft_1485_);
v___f_1497_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1497_, 0, v_toSeq_1484_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 4, v___f_1495_);
lean_ctor_set(v___x_1488_, 3, v___f_1496_);
lean_ctor_set(v___x_1488_, 2, v___f_1497_);
lean_ctor_set(v___x_1488_, 1, v___f_1490_);
lean_ctor_set(v___x_1488_, 0, v___x_1494_);
v___x_1499_ = v___x_1488_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___f_1490_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v___f_1497_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v___f_1496_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v___f_1495_);
v___x_1499_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 1, v___f_1491_);
lean_ctor_set(v___x_1481_, 0, v___x_1499_);
v___x_1501_ = v___x_1481_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v___f_1491_);
v___x_1501_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___f_1505_; lean_object* v___x_2578__overap_1506_; lean_object* v___x_1507_; 
v___x_1502_ = l_StateRefT_x27_instMonad___redArg(v___x_1501_);
v___x_1503_ = l_Lean_instInhabitedExpr;
v___x_1504_ = l_instInhabitedOfMonad___redArg(v___x_1502_, v___x_1503_);
v___f_1505_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1505_, 0, v___x_1504_);
v___x_2578__overap_1506_ = lean_panic_fn_borrowed(v___f_1505_, v_msg_1445_);
lean_dec_ref(v___f_1505_);
lean_inc(v___y_1451_);
lean_inc_ref(v___y_1450_);
lean_inc(v___y_1449_);
lean_inc_ref(v___y_1448_);
lean_inc(v___y_1447_);
lean_inc_ref(v___y_1446_);
v___x_1507_ = lean_apply_7(v___x_2578__overap_1506_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, lean_box(0));
return v___x_1507_;
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1445_ = stack[0].m_obj;
lean_object* v___y_1446_ = stack[1].m_obj;
lean_object* v___y_1447_ = stack[2].m_obj;
lean_object* v___y_1448_ = stack[3].m_obj;
lean_object* v___y_1449_ = stack[4].m_obj;
lean_object* v___y_1450_ = stack[5].m_obj;
lean_object* v___y_1451_ = stack[6].m_obj;
lean_object* v_res_1520_;
v_res_1520_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v_msg_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
stack->m_obj
 = v_res_1520_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___boxed(lean_object* v_msg_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v_msg_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1529_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1532_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1533_ = lean_unsigned_to_nat(44u);
v___x_1534_ = lean_unsigned_to_nat(316u);
v___x_1535_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1));
v___x_1536_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1537_ = l_mkPanicMessageWithDecl(v___x_1536_, v___x_1535_, v___x_1534_, v___x_1533_, v___x_1532_);
return v___x_1537_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = lean_box(0);
v___x_1542_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4));
v___x_1543_ = l_Lean_Expr_const___override(v___x_1542_, v___x_1541_);
return v___x_1543_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = lean_box(0);
v___x_1548_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7));
v___x_1549_ = l_Lean_Expr_const___override(v___x_1548_, v___x_1547_);
return v___x_1549_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = lean_box(0);
v___x_1554_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10));
v___x_1555_ = l_Lean_Expr_const___override(v___x_1554_, v___x_1553_);
return v___x_1555_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1556_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1557_ = lean_unsigned_to_nat(45u);
v___x_1558_ = lean_unsigned_to_nat(301u);
v___x_1559_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1));
v___x_1560_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1561_ = l_mkPanicMessageWithDecl(v___x_1560_, v___x_1559_, v___x_1558_, v___x_1557_, v___x_1556_);
return v___x_1561_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(lean_object* v_currentType_1562_, lean_object* v_value_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; 
switch(lean_obj_tag(v_value_1563_))
{
case 0:
{
lean_object* v_value_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1610_; 
v_value_1580_ = lean_ctor_get(v_value_1563_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_value_1563_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1582_ = v_value_1563_;
v_isShared_1583_ = v_isSharedCheck_1610_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_value_1580_);
lean_dec(v_value_1563_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1610_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
switch(lean_obj_tag(v_value_1580_))
{
case 0:
{
lean_object* v_val_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1597_; 
lean_del_object(v___x_1582_);
v_val_1584_ = lean_ctor_get(v_value_1580_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_value_1580_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1586_ = v_value_1580_;
v_isShared_1587_ = v_isSharedCheck_1597_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_val_1584_);
lean_dec(v_value_1580_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1597_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1588_ = l_Lean_maxSmallNat;
v___x_1589_ = lean_nat_dec_le(v_val_1584_, v___x_1588_);
lean_dec(v_val_1584_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1591_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v_currentType_1562_);
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_currentType_1562_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
lean_dec_ref(v_currentType_1562_);
v___x_1593_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1593_);
v___x_1595_ = v___x_1586_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
case 1:
{
lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1605_; 
lean_del_object(v___x_1582_);
lean_dec_ref(v_currentType_1562_);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_value_1580_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v_value_1580_, 0);
lean_dec(v_unused_1606_);
v___x_1599_ = v_value_1580_;
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
else
{
lean_dec(v_value_1580_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1601_);
v___x_1603_ = v___x_1599_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
default: 
{
lean_object* v___x_1608_; 
lean_dec_ref(v_value_1580_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v_currentType_1562_);
v___x_1608_ = v___x_1582_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_currentType_1562_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec_ref(v_currentType_1562_);
v___x_1611_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
return v___x_1612_;
}
case 5:
{
lean_object* v_i_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_dec_ref(v_currentType_1562_);
v_i_1613_ = lean_ctor_get(v_value_1563_, 0);
lean_inc_ref(v_i_1613_);
lean_dec_ref_known(v_value_1563_, 2);
v___x_1614_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_i_1613_);
lean_dec_ref(v_i_1613_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
case 7:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref_known(v_value_1563_, 2);
lean_dec_ref(v_currentType_1562_);
v___x_1616_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
case 9:
{
lean_object* v_fn_1618_; lean_object* v___x_1619_; 
lean_dec_ref(v_currentType_1562_);
v_fn_1618_ = lean_ctor_get(v_value_1563_, 0);
lean_inc(v_fn_1618_);
lean_dec_ref_known(v_value_1563_, 2);
v___x_1619_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_1618_, v_a_1569_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1631_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1631_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1631_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
if (lean_obj_tag(v_a_1620_) == 1)
{
lean_object* v_val_1624_; lean_object* v_type_1625_; lean_object* v___x_1627_; 
v_val_1624_ = lean_ctor_get(v_a_1620_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v_a_1620_, 1);
v_type_1625_ = lean_ctor_get(v_val_1624_, 2);
lean_inc_ref(v_type_1625_);
lean_dec(v_val_1624_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v_type_1625_);
v___x_1627_ = v___x_1622_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_type_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_del_object(v___x_1622_);
lean_dec(v_a_1620_);
v___x_1629_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12);
v___x_1630_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1629_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
return v___x_1630_;
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_a_1632_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1619_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1619_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
case 10:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec_ref_known(v_value_1563_, 2);
lean_dec_ref(v_currentType_1562_);
v___x_1640_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
return v___x_1641_;
}
case 13:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec_ref_known(v_value_1563_, 2);
lean_dec_ref(v_currentType_1562_);
v___x_1642_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
v___x_1643_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1642_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
return v___x_1643_;
}
case 14:
{
lean_dec_ref_known(v_value_1563_, 1);
lean_dec_ref(v_currentType_1562_);
v___y_1572_ = v_a_1564_;
v___y_1573_ = v_a_1565_;
v___y_1574_ = v_a_1566_;
v___y_1575_ = v_a_1567_;
v___y_1576_ = v_a_1568_;
v___y_1577_ = v_a_1569_;
goto v___jp_1571_;
}
case 15:
{
lean_dec_ref_known(v_value_1563_, 1);
lean_dec_ref(v_currentType_1562_);
v___y_1572_ = v_a_1564_;
v___y_1573_ = v_a_1565_;
v___y_1574_ = v_a_1566_;
v___y_1575_ = v_a_1567_;
v___y_1576_ = v_a_1568_;
v___y_1577_ = v_a_1569_;
goto v___jp_1571_;
}
default: 
{
lean_object* v___x_1644_; 
lean_dec(v_value_1563_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v_currentType_1562_);
return v___x_1644_;
}
}
v___jp_1571_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
v___x_1579_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1578_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
return v___x_1579_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_0interp(lean_interpreter_value* stack)
{
lean_object* v_currentType_1562_ = stack[0].m_obj;
lean_object* v_value_1563_ = stack[1].m_obj;
lean_object* v_a_1564_ = stack[2].m_obj;
lean_object* v_a_1565_ = stack[3].m_obj;
lean_object* v_a_1566_ = stack[4].m_obj;
lean_object* v_a_1567_ = stack[5].m_obj;
lean_object* v_a_1568_ = stack[6].m_obj;
lean_object* v_a_1569_ = stack[7].m_obj;
lean_object* v_res_1645_;
v_res_1645_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(v_currentType_1562_, v_value_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
stack->m_obj
 = v_res_1645_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___boxed(lean_object* v_currentType_1646_, lean_object* v_value_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(v_currentType_1646_, v_value_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
return v_res_1655_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(lean_object* v_msg_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v_toApplicative_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1729_; 
v___x_1664_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
v___x_1665_ = l_StateRefT_x27_instMonad___redArg(v___x_1664_);
v_toApplicative_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; 
v_unused_1730_ = lean_ctor_get(v___x_1665_, 1);
lean_dec(v_unused_1730_);
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1729_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_toApplicative_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1729_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v_toFunctor_1670_; lean_object* v_toSeq_1671_; lean_object* v_toSeqLeft_1672_; lean_object* v_toSeqRight_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1727_; 
v_toFunctor_1670_ = lean_ctor_get(v_toApplicative_1666_, 0);
v_toSeq_1671_ = lean_ctor_get(v_toApplicative_1666_, 2);
v_toSeqLeft_1672_ = lean_ctor_get(v_toApplicative_1666_, 3);
v_toSeqRight_1673_ = lean_ctor_get(v_toApplicative_1666_, 4);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_toApplicative_1666_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v_toApplicative_1666_, 1);
lean_dec(v_unused_1728_);
v___x_1675_ = v_toApplicative_1666_;
v_isShared_1676_ = v_isSharedCheck_1727_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_toSeqRight_1673_);
lean_inc(v_toSeqLeft_1672_);
lean_inc(v_toSeq_1671_);
lean_inc(v_toFunctor_1670_);
lean_dec(v_toApplicative_1666_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1727_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___f_1677_; lean_object* v___f_1678_; lean_object* v___f_1679_; lean_object* v___f_1680_; lean_object* v___x_1681_; lean_object* v___f_1682_; lean_object* v___f_1683_; lean_object* v___f_1684_; lean_object* v___x_1686_; 
v___f_1677_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1));
v___f_1678_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1670_);
v___f_1679_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1679_, 0, v_toFunctor_1670_);
v___f_1680_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1680_, 0, v_toFunctor_1670_);
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___f_1679_);
lean_ctor_set(v___x_1681_, 1, v___f_1680_);
v___f_1682_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1682_, 0, v_toSeqRight_1673_);
v___f_1683_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1683_, 0, v_toSeqLeft_1672_);
v___f_1684_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1684_, 0, v_toSeq_1671_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 4, v___f_1682_);
lean_ctor_set(v___x_1675_, 3, v___f_1683_);
lean_ctor_set(v___x_1675_, 2, v___f_1684_);
lean_ctor_set(v___x_1675_, 1, v___f_1677_);
lean_ctor_set(v___x_1675_, 0, v___x_1681_);
v___x_1686_ = v___x_1675_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v___f_1677_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v___f_1684_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v___f_1683_);
lean_ctor_set(v_reuseFailAlloc_1726_, 4, v___f_1682_);
v___x_1686_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1688_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 1, v___f_1678_);
lean_ctor_set(v___x_1668_, 0, v___x_1686_);
v___x_1688_ = v___x_1668_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v___f_1678_);
v___x_1688_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; lean_object* v_toApplicative_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1723_; 
v___x_1689_ = l_StateRefT_x27_instMonad___redArg(v___x_1688_);
v_toApplicative_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; 
v_unused_1724_ = lean_ctor_get(v___x_1689_, 1);
lean_dec(v_unused_1724_);
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1723_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_toApplicative_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1723_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v_toFunctor_1694_; lean_object* v_toSeq_1695_; lean_object* v_toSeqLeft_1696_; lean_object* v_toSeqRight_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1721_; 
v_toFunctor_1694_ = lean_ctor_get(v_toApplicative_1690_, 0);
v_toSeq_1695_ = lean_ctor_get(v_toApplicative_1690_, 2);
v_toSeqLeft_1696_ = lean_ctor_get(v_toApplicative_1690_, 3);
v_toSeqRight_1697_ = lean_ctor_get(v_toApplicative_1690_, 4);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_toApplicative_1690_);
if (v_isSharedCheck_1721_ == 0)
{
lean_object* v_unused_1722_; 
v_unused_1722_ = lean_ctor_get(v_toApplicative_1690_, 1);
lean_dec(v_unused_1722_);
v___x_1699_ = v_toApplicative_1690_;
v_isShared_1700_ = v_isSharedCheck_1721_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_toSeqRight_1697_);
lean_inc(v_toSeqLeft_1696_);
lean_inc(v_toSeq_1695_);
lean_inc(v_toFunctor_1694_);
lean_dec(v_toApplicative_1690_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1721_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___f_1701_; lean_object* v___f_1702_; lean_object* v___f_1703_; lean_object* v___f_1704_; lean_object* v___x_1705_; lean_object* v___f_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___x_1710_; 
v___f_1701_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3));
v___f_1702_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1694_);
v___f_1703_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1703_, 0, v_toFunctor_1694_);
v___f_1704_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1704_, 0, v_toFunctor_1694_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___f_1703_);
lean_ctor_set(v___x_1705_, 1, v___f_1704_);
v___f_1706_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1706_, 0, v_toSeqRight_1697_);
v___f_1707_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1707_, 0, v_toSeqLeft_1696_);
v___f_1708_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1708_, 0, v_toSeq_1695_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v___f_1706_);
lean_ctor_set(v___x_1699_, 3, v___f_1707_);
lean_ctor_set(v___x_1699_, 2, v___f_1708_);
lean_ctor_set(v___x_1699_, 1, v___f_1701_);
lean_ctor_set(v___x_1699_, 0, v___x_1705_);
v___x_1710_ = v___x_1699_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v___f_1701_);
lean_ctor_set(v_reuseFailAlloc_1720_, 2, v___f_1708_);
lean_ctor_set(v_reuseFailAlloc_1720_, 3, v___f_1707_);
lean_ctor_set(v_reuseFailAlloc_1720_, 4, v___f_1706_);
v___x_1710_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1712_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 1, v___f_1702_);
lean_ctor_set(v___x_1692_, 0, v___x_1710_);
v___x_1712_ = v___x_1692_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___f_1702_);
v___x_1712_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___f_1716_; lean_object* v___x_22012__overap_1717_; lean_object* v___x_1718_; 
v___x_1713_ = l_StateRefT_x27_instMonad___redArg(v___x_1712_);
v___x_1714_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
v___x_1715_ = l_instInhabitedOfMonad___redArg(v___x_1713_, v___x_1714_);
v___f_1716_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1716_, 0, v___x_1715_);
v___x_22012__overap_1717_ = lean_panic_fn_borrowed(v___f_1716_, v_msg_1656_);
lean_dec_ref(v___f_1716_);
lean_inc(v___y_1662_);
lean_inc_ref(v___y_1661_);
lean_inc(v___y_1660_);
lean_inc_ref(v___y_1659_);
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1657_);
v___x_1718_ = lean_apply_7(v___x_22012__overap_1717_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, lean_box(0));
return v___x_1718_;
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1656_ = stack[0].m_obj;
lean_object* v___y_1657_ = stack[1].m_obj;
lean_object* v___y_1658_ = stack[2].m_obj;
lean_object* v___y_1659_ = stack[3].m_obj;
lean_object* v___y_1660_ = stack[4].m_obj;
lean_object* v___y_1661_ = stack[5].m_obj;
lean_object* v___y_1662_ = stack[6].m_obj;
lean_object* v_res_1731_;
v_res_1731_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v_msg_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
stack->m_obj
 = v_res_1731_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0___boxed(lean_object* v_msg_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v_msg_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(lean_object* v_x_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0___boxed(lean_object* v_x_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(v_x_1743_);
lean_dec(v_x_1743_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4(lean_object* v_params_1745_, lean_object* v_i_1746_){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v_type_1749_; 
v___x_1747_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0);
v___x_1748_ = lean_array_get_borrowed(v___x_1747_, v_params_1745_, v_i_1746_);
v_type_1749_ = lean_ctor_get(v___x_1748_, 2);
lean_inc_ref(v_type_1749_);
return v_type_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4___boxed(lean_object* v_params_1750_, lean_object* v_i_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4(v_params_1750_, v_i_1751_);
lean_dec(v_i_1751_);
lean_dec_ref(v_params_1750_);
return v_res_1752_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(lean_object* v_fvarId_1753_, lean_object* v_code_1754_, lean_object* v_fvarId_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
uint8_t v___x_1763_; 
v___x_1763_ = l_Lean_instBEqFVarId_beq(v_fvarId_1753_, v_fvarId_1755_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec_ref(v_code_1754_);
v___x_1764_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1764_, 0, v_fvarId_1755_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
else
{
lean_object* v___x_1766_; 
lean_dec(v_fvarId_1755_);
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v_code_1754_);
return v___x_1766_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1753_ = stack[0].m_obj;
lean_object* v_code_1754_ = stack[1].m_obj;
lean_object* v_fvarId_1755_ = stack[2].m_obj;
lean_object* v___y_1756_ = stack[3].m_obj;
lean_object* v___y_1757_ = stack[4].m_obj;
lean_object* v___y_1758_ = stack[5].m_obj;
lean_object* v___y_1759_ = stack[6].m_obj;
lean_object* v___y_1760_ = stack[7].m_obj;
lean_object* v___y_1761_ = stack[8].m_obj;
lean_object* v_res_1767_;
v_res_1767_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_1753_, v_code_1754_, v_fvarId_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
stack->m_obj
 = v_res_1767_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2___boxed(lean_object* v_fvarId_1768_, lean_object* v_code_1769_, lean_object* v_fvarId_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_1768_, v_code_1769_, v_fvarId_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v_fvarId_1768_);
return v_res_1778_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(lean_object* v_typeName_1779_, lean_object* v_a_1780_, lean_object* v_alts_1781_, lean_object* v_resultType_1782_, lean_object* v_discr_1783_, lean_object* v_code_1784_, lean_object* v_discr_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_currDeclResultType_1793_; size_t v___x_1798_; size_t v___x_1799_; uint8_t v___x_1800_; 
v_currDeclResultType_1793_ = lean_ctor_get(v___y_1786_, 1);
v___x_1798_ = lean_ptr_addr(v_alts_1781_);
v___x_1799_ = lean_ptr_addr(v_a_1780_);
v___x_1800_ = lean_usize_dec_eq(v___x_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_dec_ref(v_code_1784_);
goto v___jp_1794_;
}
else
{
size_t v___x_1801_; size_t v___x_1802_; uint8_t v___x_1803_; 
v___x_1801_ = lean_ptr_addr(v_resultType_1782_);
v___x_1802_ = lean_ptr_addr(v_currDeclResultType_1793_);
v___x_1803_ = lean_usize_dec_eq(v___x_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_dec_ref(v_code_1784_);
goto v___jp_1794_;
}
else
{
uint8_t v___x_1804_; 
v___x_1804_ = l_Lean_instBEqFVarId_beq(v_discr_1783_, v_discr_1785_);
if (v___x_1804_ == 0)
{
lean_dec_ref(v_code_1784_);
goto v___jp_1794_;
}
else
{
lean_object* v___x_1805_; 
lean_dec(v_discr_1785_);
lean_dec_ref(v_a_1780_);
lean_dec(v_typeName_1779_);
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_code_1784_);
return v___x_1805_;
}
}
}
v___jp_1794_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_inc_ref(v_currDeclResultType_1793_);
v___x_1795_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1795_, 0, v_typeName_1779_);
lean_ctor_set(v___x_1795_, 1, v_currDeclResultType_1793_);
lean_ctor_set(v___x_1795_, 2, v_discr_1785_);
lean_ctor_set(v___x_1795_, 3, v_a_1780_);
v___x_1796_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeName_1779_ = stack[0].m_obj;
lean_object* v_a_1780_ = stack[1].m_obj;
lean_object* v_alts_1781_ = stack[2].m_obj;
lean_object* v_resultType_1782_ = stack[3].m_obj;
lean_object* v_discr_1783_ = stack[4].m_obj;
lean_object* v_code_1784_ = stack[5].m_obj;
lean_object* v_discr_1785_ = stack[6].m_obj;
lean_object* v___y_1786_ = stack[7].m_obj;
lean_object* v___y_1787_ = stack[8].m_obj;
lean_object* v___y_1788_ = stack[9].m_obj;
lean_object* v___y_1789_ = stack[10].m_obj;
lean_object* v___y_1790_ = stack[11].m_obj;
lean_object* v___y_1791_ = stack[12].m_obj;
lean_object* v_res_1806_;
v_res_1806_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_1779_, v_a_1780_, v_alts_1781_, v_resultType_1782_, v_discr_1783_, v_code_1784_, v_discr_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
stack->m_obj
 = v_res_1806_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1___boxed(lean_object* v_typeName_1807_, lean_object* v_a_1808_, lean_object* v_alts_1809_, lean_object* v_resultType_1810_, lean_object* v_discr_1811_, lean_object* v_code_1812_, lean_object* v_discr_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_1807_, v_a_1808_, v_alts_1809_, v_resultType_1810_, v_discr_1811_, v_code_1812_, v_discr_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v_discr_1811_);
lean_dec_ref(v_resultType_1810_);
lean_dec_ref(v_alts_1809_);
return v_res_1821_;
}
}
lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(lean_object* v_alt_1822_, lean_object* v_f_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v___y_1832_; 
switch(lean_obj_tag(v_alt_1822_))
{
case 0:
{
lean_object* v_code_1851_; 
v_code_1851_ = lean_ctor_get(v_alt_1822_, 2);
lean_inc_ref(v_code_1851_);
v___y_1832_ = v_code_1851_;
goto v___jp_1831_;
}
case 1:
{
lean_object* v_code_1852_; 
v_code_1852_ = lean_ctor_get(v_alt_1822_, 1);
lean_inc_ref(v_code_1852_);
v___y_1832_ = v_code_1852_;
goto v___jp_1831_;
}
default: 
{
lean_object* v_code_1853_; 
v_code_1853_ = lean_ctor_get(v_alt_1822_, 0);
lean_inc_ref(v_code_1853_);
v___y_1832_ = v_code_1853_;
goto v___jp_1831_;
}
}
v___jp_1831_:
{
lean_object* v___x_1833_; 
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1824_);
v___x_1833_ = lean_apply_8(v_f_1823_, v___y_1832_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, lean_box(0));
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1842_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1838_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1822_, v_a_1834_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1838_);
v___x_1840_ = v___x_1836_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec_ref(v_alt_1822_);
v_a_1843_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1833_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1833_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_alt_1822_ = stack[0].m_obj;
lean_object* v_f_1823_ = stack[1].m_obj;
lean_object* v___y_1824_ = stack[2].m_obj;
lean_object* v___y_1825_ = stack[3].m_obj;
lean_object* v___y_1826_ = stack[4].m_obj;
lean_object* v___y_1827_ = stack[5].m_obj;
lean_object* v___y_1828_ = stack[6].m_obj;
lean_object* v___y_1829_ = stack[7].m_obj;
lean_object* v_res_1854_;
v_res_1854_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_alt_1822_, v_f_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
stack->m_obj
 = v_res_1854_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg___boxed(lean_object* v_alt_1855_, lean_object* v_f_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_alt_1855_, v_f_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1864_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(lean_object* v_fvarId_1865_, lean_object* v_i_1866_, lean_object* v_offset_1867_, lean_object* v_ty_1868_, lean_object* v_a_1869_, lean_object* v_y_1870_, lean_object* v_k_1871_, lean_object* v_code_1872_, lean_object* v_y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
size_t v___x_1881_; uint8_t v___x_1882_; 
v___x_1881_ = lean_ptr_addr(v_fvarId_1865_);
v___x_1882_ = lean_usize_dec_eq(v___x_1881_, v___x_1881_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_dec_ref(v_code_1872_);
v___x_1883_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1883_, 0, v_fvarId_1865_);
lean_ctor_set(v___x_1883_, 1, v_i_1866_);
lean_ctor_set(v___x_1883_, 2, v_offset_1867_);
lean_ctor_set(v___x_1883_, 3, v_y_1873_);
lean_ctor_set(v___x_1883_, 4, v_ty_1868_);
lean_ctor_set(v___x_1883_, 5, v_a_1869_);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
else
{
uint8_t v___x_1885_; 
v___x_1885_ = lean_nat_dec_eq(v_i_1866_, v_i_1866_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_dec_ref(v_code_1872_);
v___x_1886_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1886_, 0, v_fvarId_1865_);
lean_ctor_set(v___x_1886_, 1, v_i_1866_);
lean_ctor_set(v___x_1886_, 2, v_offset_1867_);
lean_ctor_set(v___x_1886_, 3, v_y_1873_);
lean_ctor_set(v___x_1886_, 4, v_ty_1868_);
lean_ctor_set(v___x_1886_, 5, v_a_1869_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
else
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_nat_dec_eq(v_offset_1867_, v_offset_1867_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec_ref(v_code_1872_);
v___x_1889_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1889_, 0, v_fvarId_1865_);
lean_ctor_set(v___x_1889_, 1, v_i_1866_);
lean_ctor_set(v___x_1889_, 2, v_offset_1867_);
lean_ctor_set(v___x_1889_, 3, v_y_1873_);
lean_ctor_set(v___x_1889_, 4, v_ty_1868_);
lean_ctor_set(v___x_1889_, 5, v_a_1869_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
else
{
size_t v___x_1891_; size_t v___x_1892_; uint8_t v___x_1893_; 
v___x_1891_ = lean_ptr_addr(v_y_1870_);
v___x_1892_ = lean_ptr_addr(v_y_1873_);
v___x_1893_ = lean_usize_dec_eq(v___x_1891_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec_ref(v_code_1872_);
v___x_1894_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1894_, 0, v_fvarId_1865_);
lean_ctor_set(v___x_1894_, 1, v_i_1866_);
lean_ctor_set(v___x_1894_, 2, v_offset_1867_);
lean_ctor_set(v___x_1894_, 3, v_y_1873_);
lean_ctor_set(v___x_1894_, 4, v_ty_1868_);
lean_ctor_set(v___x_1894_, 5, v_a_1869_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
else
{
size_t v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = lean_ptr_addr(v_ty_1868_);
v___x_1897_ = lean_usize_dec_eq(v___x_1896_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
lean_dec_ref(v_code_1872_);
v___x_1898_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1898_, 0, v_fvarId_1865_);
lean_ctor_set(v___x_1898_, 1, v_i_1866_);
lean_ctor_set(v___x_1898_, 2, v_offset_1867_);
lean_ctor_set(v___x_1898_, 3, v_y_1873_);
lean_ctor_set(v___x_1898_, 4, v_ty_1868_);
lean_ctor_set(v___x_1898_, 5, v_a_1869_);
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
return v___x_1899_;
}
else
{
size_t v___x_1900_; size_t v___x_1901_; uint8_t v___x_1902_; 
v___x_1900_ = lean_ptr_addr(v_k_1871_);
v___x_1901_ = lean_ptr_addr(v_a_1869_);
v___x_1902_ = lean_usize_dec_eq(v___x_1900_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_dec_ref(v_code_1872_);
v___x_1903_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1903_, 0, v_fvarId_1865_);
lean_ctor_set(v___x_1903_, 1, v_i_1866_);
lean_ctor_set(v___x_1903_, 2, v_offset_1867_);
lean_ctor_set(v___x_1903_, 3, v_y_1873_);
lean_ctor_set(v___x_1903_, 4, v_ty_1868_);
lean_ctor_set(v___x_1903_, 5, v_a_1869_);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
return v___x_1904_;
}
else
{
lean_object* v___x_1905_; 
lean_dec(v_y_1873_);
lean_dec_ref(v_a_1869_);
lean_dec_ref(v_ty_1868_);
lean_dec(v_offset_1867_);
lean_dec(v_i_1866_);
lean_dec(v_fvarId_1865_);
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_code_1872_);
return v___x_1905_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1865_ = stack[0].m_obj;
lean_object* v_i_1866_ = stack[1].m_obj;
lean_object* v_offset_1867_ = stack[2].m_obj;
lean_object* v_ty_1868_ = stack[3].m_obj;
lean_object* v_a_1869_ = stack[4].m_obj;
lean_object* v_y_1870_ = stack[5].m_obj;
lean_object* v_k_1871_ = stack[6].m_obj;
lean_object* v_code_1872_ = stack[7].m_obj;
lean_object* v_y_1873_ = stack[8].m_obj;
lean_object* v___y_1874_ = stack[9].m_obj;
lean_object* v___y_1875_ = stack[10].m_obj;
lean_object* v___y_1876_ = stack[11].m_obj;
lean_object* v___y_1877_ = stack[12].m_obj;
lean_object* v___y_1878_ = stack[13].m_obj;
lean_object* v___y_1879_ = stack[14].m_obj;
lean_object* v_res_1906_;
v_res_1906_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_1865_, v_i_1866_, v_offset_1867_, v_ty_1868_, v_a_1869_, v_y_1870_, v_k_1871_, v_code_1872_, v_y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
stack->m_obj
 = v_res_1906_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4___boxed(lean_object* v_fvarId_1907_, lean_object* v_i_1908_, lean_object* v_offset_1909_, lean_object* v_ty_1910_, lean_object* v_a_1911_, lean_object* v_y_1912_, lean_object* v_k_1913_, lean_object* v_code_1914_, lean_object* v_y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_1907_, v_i_1908_, v_offset_1909_, v_ty_1910_, v_a_1911_, v_y_1912_, v_k_1913_, v_code_1914_, v_y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec_ref(v_k_1913_);
lean_dec(v_y_1912_);
return v_res_1923_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(lean_object* v_fvarId_1924_, lean_object* v_i_1925_, lean_object* v_a_1926_, lean_object* v_y_1927_, lean_object* v_k_1928_, lean_object* v_code_1929_, lean_object* v_y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
size_t v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = lean_ptr_addr(v_fvarId_1924_);
v___x_1939_ = lean_usize_dec_eq(v___x_1938_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec_ref(v_code_1929_);
v___x_1940_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1940_, 0, v_fvarId_1924_);
lean_ctor_set(v___x_1940_, 1, v_i_1925_);
lean_ctor_set(v___x_1940_, 2, v_y_1930_);
lean_ctor_set(v___x_1940_, 3, v_a_1926_);
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
return v___x_1941_;
}
else
{
uint8_t v___x_1942_; 
v___x_1942_ = lean_nat_dec_eq(v_i_1925_, v_i_1925_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec_ref(v_code_1929_);
v___x_1943_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1943_, 0, v_fvarId_1924_);
lean_ctor_set(v___x_1943_, 1, v_i_1925_);
lean_ctor_set(v___x_1943_, 2, v_y_1930_);
lean_ctor_set(v___x_1943_, 3, v_a_1926_);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
else
{
size_t v___x_1945_; size_t v___x_1946_; uint8_t v___x_1947_; 
v___x_1945_ = lean_ptr_addr(v_y_1927_);
v___x_1946_ = lean_ptr_addr(v_y_1930_);
v___x_1947_ = lean_usize_dec_eq(v___x_1945_, v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec_ref(v_code_1929_);
v___x_1948_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1948_, 0, v_fvarId_1924_);
lean_ctor_set(v___x_1948_, 1, v_i_1925_);
lean_ctor_set(v___x_1948_, 2, v_y_1930_);
lean_ctor_set(v___x_1948_, 3, v_a_1926_);
v___x_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
return v___x_1949_;
}
else
{
size_t v___x_1950_; size_t v___x_1951_; uint8_t v___x_1952_; 
v___x_1950_ = lean_ptr_addr(v_k_1928_);
v___x_1951_ = lean_ptr_addr(v_a_1926_);
v___x_1952_ = lean_usize_dec_eq(v___x_1950_, v___x_1951_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_dec_ref(v_code_1929_);
v___x_1953_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1953_, 0, v_fvarId_1924_);
lean_ctor_set(v___x_1953_, 1, v_i_1925_);
lean_ctor_set(v___x_1953_, 2, v_y_1930_);
lean_ctor_set(v___x_1953_, 3, v_a_1926_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
else
{
lean_object* v___x_1955_; 
lean_dec(v_y_1930_);
lean_dec_ref(v_a_1926_);
lean_dec(v_i_1925_);
lean_dec(v_fvarId_1924_);
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v_code_1929_);
return v___x_1955_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1924_ = stack[0].m_obj;
lean_object* v_i_1925_ = stack[1].m_obj;
lean_object* v_a_1926_ = stack[2].m_obj;
lean_object* v_y_1927_ = stack[3].m_obj;
lean_object* v_k_1928_ = stack[4].m_obj;
lean_object* v_code_1929_ = stack[5].m_obj;
lean_object* v_y_1930_ = stack[6].m_obj;
lean_object* v___y_1931_ = stack[7].m_obj;
lean_object* v___y_1932_ = stack[8].m_obj;
lean_object* v___y_1933_ = stack[9].m_obj;
lean_object* v___y_1934_ = stack[10].m_obj;
lean_object* v___y_1935_ = stack[11].m_obj;
lean_object* v___y_1936_ = stack[12].m_obj;
lean_object* v_res_1956_;
v_res_1956_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_1924_, v_i_1925_, v_a_1926_, v_y_1927_, v_k_1928_, v_code_1929_, v_y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
stack->m_obj
 = v_res_1956_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3___boxed(lean_object* v_fvarId_1957_, lean_object* v_i_1958_, lean_object* v_a_1959_, lean_object* v_y_1960_, lean_object* v_k_1961_, lean_object* v_code_1962_, lean_object* v_y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_1957_, v_i_1958_, v_a_1959_, v_y_1960_, v_k_1961_, v_code_1962_, v_y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec_ref(v_k_1961_);
lean_dec(v_y_1960_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(lean_object* v_params_1972_, lean_object* v_i_1973_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v_type_1976_; 
v___x_1974_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0);
v___x_1975_ = lean_array_get_borrowed(v___x_1974_, v_params_1972_, v_i_1973_);
v_type_1976_ = lean_ctor_get(v___x_1975_, 2);
lean_inc_ref(v_type_1976_);
return v_type_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed(lean_object* v_params_1977_, lean_object* v_i_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(v_params_1977_, v_i_1978_);
lean_dec(v_i_1978_);
lean_dec_ref(v_params_1977_);
return v_res_1979_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1981_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1982_ = lean_unsigned_to_nat(44u);
v___x_1983_ = lean_unsigned_to_nat(353u);
v___x_1984_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_1985_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1986_ = l_mkPanicMessageWithDecl(v___x_1985_, v___x_1984_, v___x_1983_, v___x_1982_, v___x_1981_);
return v___x_1986_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1988_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1989_ = lean_unsigned_to_nat(45u);
v___x_1990_ = lean_unsigned_to_nat(336u);
v___x_1991_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_1992_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1993_ = l_mkPanicMessageWithDecl(v___x_1992_, v___x_1991_, v___x_1990_, v___x_1989_, v___x_1988_);
return v___x_1993_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1994_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1995_ = lean_unsigned_to_nat(45u);
v___x_1996_ = lean_unsigned_to_nat(341u);
v___x_1997_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_1998_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1999_ = l_mkPanicMessageWithDecl(v___x_1998_, v___x_1997_, v___x_1996_, v___x_1995_, v___x_1994_);
return v___x_1999_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(lean_object* v_code_2000_, lean_object* v_decl_2001_, lean_object* v_k_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v_type_2029_; lean_object* v_value_2030_; lean_object* v___f_2031_; lean_object* v___x_2032_; 
v_type_2029_ = lean_ctor_get(v_decl_2001_, 2);
v_value_2030_ = lean_ctor_get(v_decl_2001_, 3);
lean_inc_n(v_value_2030_, 2);
v___f_2031_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2));
lean_inc_ref(v_type_2029_);
v___x_2032_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(v_type_2029_, v_value_2030_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; uint8_t v___x_2034_; lean_object* v___x_2035_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc_n(v_a_2033_, 2);
lean_dec_ref_known(v___x_2032_, 1);
v___x_2034_ = 1;
v___x_2035_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_2034_, v_decl_2001_, v_a_2033_, v_value_2030_, v_a_2006_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2037_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2035_, 1);
v___x_2037_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2513_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2513_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2513_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v_value_2042_; lean_object* v___y_2044_; 
v_value_2042_ = lean_ctor_get(v_a_2036_, 3);
switch(lean_obj_tag(v_value_2042_))
{
case 4:
{
lean_object* v_args_2104_; lean_object* v___x_2105_; 
lean_del_object(v___x_2040_);
lean_dec(v_a_2033_);
v_args_2104_ = lean_ctor_get(v_value_2042_, 1);
v___x_2105_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2104_, v___f_2031_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v_fst_2107_; lean_object* v_snd_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v_fst_2107_ = lean_ctor_get(v_a_2106_, 0);
lean_inc(v_fst_2107_);
v_snd_2108_ = lean_ctor_get(v_a_2106_, 1);
lean_inc(v_snd_2108_);
lean_dec(v_a_2106_);
lean_inc_ref(v_value_2042_);
v___x_2109_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_value_2042_, v_fst_2107_);
v___x_2110_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2034_, v_a_2036_, v___x_2109_, v_a_2006_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2112_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v___x_2112_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_2000_, v_a_2111_, v_a_2038_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2121_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2121_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2121_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2117_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_2108_, v_a_2113_);
lean_dec(v_snd_2108_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2117_);
v___x_2119_ = v___x_2115_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
else
{
lean_dec(v_snd_2108_);
return v___x_2112_;
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_snd_2108_);
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v_a_2122_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2110_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2110_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
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
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
lean_dec_ref(v_code_2000_);
v_a_2130_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2105_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2105_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
case 5:
{
lean_object* v_i_2138_; lean_object* v_args_2139_; uint8_t v___y_2141_; uint8_t v___x_2257_; 
v_i_2138_ = lean_ctor_get(v_value_2042_, 0);
v_args_2139_ = lean_ctor_get(v_value_2042_, 1);
v___x_2257_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_i_2138_);
if (v___x_2257_ == 0)
{
v___y_2141_ = v___x_2257_;
goto v___jp_2140_;
}
else
{
uint8_t v___x_2258_; 
v___x_2258_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_2033_);
v___y_2141_ = v___x_2258_;
goto v___jp_2140_;
}
v___jp_2140_:
{
if (v___y_2141_ == 0)
{
lean_object* v___x_2142_; 
lean_del_object(v___x_2040_);
lean_dec(v_a_2033_);
v___x_2142_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2139_, v___f_2031_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v_fst_2144_; lean_object* v_snd_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v_fst_2144_ = lean_ctor_get(v_a_2143_, 0);
lean_inc(v_fst_2144_);
v_snd_2145_ = lean_ctor_get(v_a_2143_, 1);
lean_inc(v_snd_2145_);
lean_dec(v_a_2143_);
lean_inc_ref(v_value_2042_);
v___x_2146_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_value_2042_, v_fst_2144_);
v___x_2147_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2034_, v_a_2036_, v___x_2146_, v_a_2006_);
if (lean_obj_tag(v___x_2147_) == 0)
{
if (lean_obj_tag(v_code_2000_) == 0)
{
lean_object* v_a_2148_; lean_object* v_decl_2149_; lean_object* v_k_2150_; size_t v___x_2151_; size_t v___x_2152_; uint8_t v___x_2153_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v_decl_2149_ = lean_ctor_get(v_code_2000_, 0);
v_k_2150_ = lean_ctor_get(v_code_2000_, 1);
v___x_2151_ = lean_ptr_addr(v_k_2150_);
v___x_2152_ = lean_ptr_addr(v_a_2038_);
v___x_2153_ = lean_usize_dec_eq(v___x_2151_, v___x_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
v_isSharedCheck_2160_ = !lean_is_exclusive(v_code_2000_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; lean_object* v_unused_2162_; 
v_unused_2161_ = lean_ctor_get(v_code_2000_, 1);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_code_2000_, 0);
lean_dec(v_unused_2162_);
v___x_2155_ = v_code_2000_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_dec(v_code_2000_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v_a_2038_);
lean_ctor_set(v___x_2155_, 0, v_a_2148_);
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2148_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_a_2038_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
v___y_2016_ = v_snd_2145_;
v___y_2017_ = v___x_2158_;
goto v___jp_2015_;
}
}
}
else
{
size_t v___x_2163_; size_t v___x_2164_; uint8_t v___x_2165_; 
v___x_2163_ = lean_ptr_addr(v_decl_2149_);
v___x_2164_ = lean_ptr_addr(v_a_2148_);
v___x_2165_ = lean_usize_dec_eq(v___x_2163_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
v_isSharedCheck_2172_ = !lean_is_exclusive(v_code_2000_);
if (v_isSharedCheck_2172_ == 0)
{
lean_object* v_unused_2173_; lean_object* v_unused_2174_; 
v_unused_2173_ = lean_ctor_get(v_code_2000_, 1);
lean_dec(v_unused_2173_);
v_unused_2174_ = lean_ctor_get(v_code_2000_, 0);
lean_dec(v_unused_2174_);
v___x_2167_ = v_code_2000_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_dec(v_code_2000_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 1, v_a_2038_);
lean_ctor_set(v___x_2167_, 0, v_a_2148_);
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2148_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_a_2038_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
v___y_2016_ = v_snd_2145_;
v___y_2017_ = v___x_2170_;
goto v___jp_2015_;
}
}
}
else
{
lean_dec(v_a_2148_);
lean_dec(v_a_2038_);
v___y_2016_ = v_snd_2145_;
v___y_2017_ = v_code_2000_;
goto v___jp_2015_;
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec_ref_known(v___x_2147_, 1);
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v___x_2175_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2176_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2175_);
v___y_2016_ = v_snd_2145_;
v___y_2017_ = v___x_2176_;
goto v___jp_2015_;
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v_snd_2145_);
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v_a_2177_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2147_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2147_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
lean_dec_ref(v_code_2000_);
v_a_2185_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2142_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2142_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
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
lean_object* v_cidx_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v_cidx_2193_ = lean_ctor_get(v_i_2138_, 1);
v___x_2194_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_2033_, v_cidx_2193_);
lean_dec(v_a_2033_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2194_);
v___x_2196_ = v___x_2040_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2034_, v_a_2036_, v___x_2196_, v_a_2006_);
if (lean_obj_tag(v___x_2197_) == 0)
{
if (lean_obj_tag(v_code_2000_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2237_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2237_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2237_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v_decl_2202_; lean_object* v_k_2203_; size_t v___x_2204_; size_t v___x_2205_; uint8_t v___x_2206_; 
v_decl_2202_ = lean_ctor_get(v_code_2000_, 0);
v_k_2203_ = lean_ctor_get(v_code_2000_, 1);
v___x_2204_ = lean_ptr_addr(v_k_2203_);
v___x_2205_ = lean_ptr_addr(v_a_2038_);
v___x_2206_ = lean_usize_dec_eq(v___x_2204_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2216_; 
v_isSharedCheck_2216_ = !lean_is_exclusive(v_code_2000_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; lean_object* v_unused_2218_; 
v_unused_2217_ = lean_ctor_get(v_code_2000_, 1);
lean_dec(v_unused_2217_);
v_unused_2218_ = lean_ctor_get(v_code_2000_, 0);
lean_dec(v_unused_2218_);
v___x_2208_ = v_code_2000_;
v_isShared_2209_ = v_isSharedCheck_2216_;
goto v_resetjp_2207_;
}
else
{
lean_dec(v_code_2000_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2216_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 1, v_a_2038_);
lean_ctor_set(v___x_2208_, 0, v_a_2198_);
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2198_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_a_2038_);
v___x_2211_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2213_; 
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2211_);
v___x_2213_ = v___x_2200_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
size_t v___x_2219_; size_t v___x_2220_; uint8_t v___x_2221_; 
v___x_2219_ = lean_ptr_addr(v_decl_2202_);
v___x_2220_ = lean_ptr_addr(v_a_2198_);
v___x_2221_ = lean_usize_dec_eq(v___x_2219_, v___x_2220_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2231_; 
v_isSharedCheck_2231_ = !lean_is_exclusive(v_code_2000_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; lean_object* v_unused_2233_; 
v_unused_2232_ = lean_ctor_get(v_code_2000_, 1);
lean_dec(v_unused_2232_);
v_unused_2233_ = lean_ctor_get(v_code_2000_, 0);
lean_dec(v_unused_2233_);
v___x_2223_ = v_code_2000_;
v_isShared_2224_ = v_isSharedCheck_2231_;
goto v_resetjp_2222_;
}
else
{
lean_dec(v_code_2000_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2231_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 1, v_a_2038_);
lean_ctor_set(v___x_2223_, 0, v_a_2198_);
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2198_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_a_2038_);
v___x_2226_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2228_; 
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2226_);
v___x_2228_ = v___x_2200_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v___x_2235_; 
lean_dec(v_a_2198_);
lean_dec(v_a_2038_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v_code_2000_);
v___x_2235_ = v___x_2200_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_code_2000_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
else
{
lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2246_ == 0)
{
lean_object* v_unused_2247_; 
v_unused_2247_ = lean_ctor_get(v___x_2197_, 0);
lean_dec(v_unused_2247_);
v___x_2239_ = v___x_2197_;
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
else
{
lean_dec(v___x_2197_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2241_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2242_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2241_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2242_);
v___x_2244_ = v___x_2239_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
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
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v_a_2248_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2197_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2197_);
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
}
}
case 6:
{
lean_inc_ref(v_value_2042_);
lean_del_object(v___x_2040_);
v___y_2044_ = v_a_2006_;
goto v___jp_2043_;
}
case 7:
{
lean_inc_ref(v_value_2042_);
lean_del_object(v___x_2040_);
v___y_2044_ = v_a_2006_;
goto v___jp_2043_;
}
case 9:
{
lean_object* v_fn_2259_; lean_object* v_args_2260_; lean_object* v___x_2261_; 
lean_del_object(v___x_2040_);
lean_dec(v_a_2033_);
v_fn_2259_ = lean_ctor_get(v_value_2042_, 0);
v_args_2260_ = lean_ctor_get(v_value_2042_, 1);
lean_inc(v_fn_2259_);
v___x_2261_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_2259_, v_a_2008_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2261_, 1);
if (lean_obj_tag(v_a_2262_) == 1)
{
lean_object* v_val_2263_; lean_object* v_type_2264_; lean_object* v_params_2265_; lean_object* v___f_2266_; lean_object* v___x_2267_; 
v_val_2263_ = lean_ctor_get(v_a_2262_, 0);
lean_inc(v_val_2263_);
lean_dec_ref_known(v_a_2262_, 1);
v_type_2264_ = lean_ctor_get(v_val_2263_, 2);
lean_inc_ref(v_type_2264_);
v_params_2265_ = lean_ctor_get(v_val_2263_, 3);
lean_inc_ref(v_params_2265_);
lean_dec(v_val_2263_);
v___f_2266_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4___boxed), 2, 1);
lean_closure_set(v___f_2266_, 0, v_params_2265_);
v___x_2267_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2260_, v___f_2266_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v_fst_2269_; lean_object* v_snd_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v_fst_2269_ = lean_ctor_get(v_a_2268_, 0);
lean_inc(v_fst_2269_);
v_snd_2270_ = lean_ctor_get(v_a_2268_, 1);
lean_inc(v_snd_2270_);
lean_dec(v_a_2268_);
lean_inc_ref(v_value_2042_);
v___x_2271_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_value_2042_, v_fst_2269_);
v___x_2272_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2034_, v_a_2036_, v___x_2271_, v_a_2006_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2274_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
v___x_2274_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(v_code_2000_, v_a_2273_, v_type_2264_, v_a_2038_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
lean_dec_ref(v_type_2264_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2283_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2283_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2283_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2279_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_2270_, v_a_2275_);
lean_dec(v_snd_2270_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2279_);
v___x_2281_ = v___x_2277_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
else
{
lean_dec(v_snd_2270_);
return v___x_2274_;
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec(v_snd_2270_);
lean_dec_ref(v_type_2264_);
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v_a_2284_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2272_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2272_);
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
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v_type_2264_);
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
lean_dec_ref(v_code_2000_);
v_a_2292_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2267_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2267_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec(v_a_2262_);
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
lean_dec_ref(v_code_2000_);
v___x_2300_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3);
v___x_2301_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2300_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
return v___x_2301_;
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
lean_dec_ref(v_code_2000_);
v_a_2302_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2261_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2261_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
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
case 10:
{
lean_object* v_fn_2310_; lean_object* v_args_2311_; lean_object* v___x_2312_; 
lean_del_object(v___x_2040_);
lean_dec(v_a_2033_);
v_fn_2310_ = lean_ctor_get(v_value_2042_, 0);
v_args_2311_ = lean_ctor_get(v_value_2042_, 1);
lean_inc(v_fn_2310_);
v___x_2312_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_2310_, v_a_2008_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2312_, 1);
if (lean_obj_tag(v_a_2313_) == 1)
{
lean_object* v_val_2314_; lean_object* v___x_2315_; 
v_val_2314_ = lean_ctor_get(v_a_2313_, 0);
lean_inc(v_val_2314_);
lean_dec_ref_known(v_a_2313_, 1);
v___x_2315_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_val_2314_, v_a_2008_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___y_2318_; uint8_t v___x_2370_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2370_ = lean_unbox(v_a_2316_);
lean_dec(v_a_2316_);
if (v___x_2370_ == 0)
{
lean_inc(v_fn_2310_);
v___y_2318_ = v_fn_2310_;
goto v___jp_2317_;
}
else
{
lean_object* v___x_2371_; 
lean_inc(v_fn_2310_);
v___x_2371_ = l_Lean_Compiler_LCNF_mkBoxedName(v_fn_2310_);
v___y_2318_ = v___x_2371_;
goto v___jp_2317_;
}
v___jp_2317_:
{
lean_object* v___x_2319_; 
v___x_2319_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2311_, v___f_2031_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v_fst_2321_; lean_object* v_snd_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v_fst_2321_ = lean_ctor_get(v_a_2320_, 0);
lean_inc(v_fst_2321_);
v_snd_2322_ = lean_ctor_get(v_a_2320_, 1);
lean_inc(v_snd_2322_);
lean_dec(v_a_2320_);
v___x_2323_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updatePapImp___redArg(v_value_2042_, v___y_2318_, v_fst_2321_);
v___x_2324_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2034_, v_a_2036_, v___x_2323_, v_a_2006_);
if (lean_obj_tag(v___x_2324_) == 0)
{
if (lean_obj_tag(v_code_2000_) == 0)
{
lean_object* v_a_2325_; lean_object* v_decl_2326_; lean_object* v_k_2327_; size_t v___x_2328_; size_t v___x_2329_; uint8_t v___x_2330_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v_decl_2326_ = lean_ctor_get(v_code_2000_, 0);
v_k_2327_ = lean_ctor_get(v_code_2000_, 1);
v___x_2328_ = lean_ptr_addr(v_k_2327_);
v___x_2329_ = lean_ptr_addr(v_a_2038_);
v___x_2330_ = lean_usize_dec_eq(v___x_2328_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
v_isSharedCheck_2337_ = !lean_is_exclusive(v_code_2000_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; lean_object* v_unused_2339_; 
v_unused_2338_ = lean_ctor_get(v_code_2000_, 1);
lean_dec(v_unused_2338_);
v_unused_2339_ = lean_ctor_get(v_code_2000_, 0);
lean_dec(v_unused_2339_);
v___x_2332_ = v_code_2000_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_dec(v_code_2000_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 1, v_a_2038_);
lean_ctor_set(v___x_2332_, 0, v_a_2325_);
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2325_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_a_2038_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
v___y_2011_ = v_snd_2322_;
v___y_2012_ = v___x_2335_;
goto v___jp_2010_;
}
}
}
else
{
size_t v___x_2340_; size_t v___x_2341_; uint8_t v___x_2342_; 
v___x_2340_ = lean_ptr_addr(v_decl_2326_);
v___x_2341_ = lean_ptr_addr(v_a_2325_);
v___x_2342_ = lean_usize_dec_eq(v___x_2340_, v___x_2341_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
v_isSharedCheck_2349_ = !lean_is_exclusive(v_code_2000_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; lean_object* v_unused_2351_; 
v_unused_2350_ = lean_ctor_get(v_code_2000_, 1);
lean_dec(v_unused_2350_);
v_unused_2351_ = lean_ctor_get(v_code_2000_, 0);
lean_dec(v_unused_2351_);
v___x_2344_ = v_code_2000_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_dec(v_code_2000_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 1, v_a_2038_);
lean_ctor_set(v___x_2344_, 0, v_a_2325_);
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2325_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_a_2038_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
v___y_2011_ = v_snd_2322_;
v___y_2012_ = v___x_2347_;
goto v___jp_2010_;
}
}
}
else
{
lean_dec(v_a_2325_);
lean_dec(v_a_2038_);
v___y_2011_ = v_snd_2322_;
v___y_2012_ = v_code_2000_;
goto v___jp_2010_;
}
}
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec_ref_known(v___x_2324_, 1);
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v___x_2352_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2353_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2352_);
v___y_2011_ = v_snd_2322_;
v___y_2012_ = v___x_2353_;
goto v___jp_2010_;
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v_snd_2322_);
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v_a_2354_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2324_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2324_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec(v___y_2318_);
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
lean_dec_ref(v_code_2000_);
v_a_2362_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2319_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2319_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
lean_dec_ref(v_code_2000_);
v_a_2372_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2315_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2315_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
lean_dec(v_a_2313_);
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
lean_dec_ref(v_code_2000_);
v___x_2380_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4);
v___x_2381_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2380_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
return v___x_2381_;
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
lean_dec_ref(v_code_2000_);
v_a_2382_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2312_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2312_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
case 11:
{
lean_inc_ref(v_value_2042_);
lean_del_object(v___x_2040_);
v___y_2044_ = v_a_2006_;
goto v___jp_2043_;
}
case 12:
{
lean_object* v_args_2390_; lean_object* v___x_2391_; 
lean_del_object(v___x_2040_);
lean_dec(v_a_2033_);
v_args_2390_ = lean_ctor_get(v_value_2042_, 2);
v___x_2391_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2390_, v___f_2031_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v_fst_2393_; lean_object* v_snd_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v_fst_2393_ = lean_ctor_get(v_a_2392_, 0);
lean_inc(v_fst_2393_);
v_snd_2394_ = lean_ctor_get(v_a_2392_, 1);
lean_inc(v_snd_2394_);
lean_dec(v_a_2392_);
lean_inc_ref(v_value_2042_);
v___x_2395_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_value_2042_, v_fst_2393_);
v___x_2396_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2034_, v_a_2036_, v___x_2395_, v_a_2006_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2435_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2435_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2435_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___y_2402_; 
if (lean_obj_tag(v_code_2000_) == 0)
{
lean_object* v_decl_2407_; lean_object* v_k_2408_; size_t v___x_2409_; size_t v___x_2410_; uint8_t v___x_2411_; 
v_decl_2407_ = lean_ctor_get(v_code_2000_, 0);
v_k_2408_ = lean_ctor_get(v_code_2000_, 1);
v___x_2409_ = lean_ptr_addr(v_k_2408_);
v___x_2410_ = lean_ptr_addr(v_a_2038_);
v___x_2411_ = lean_usize_dec_eq(v___x_2409_, v___x_2410_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
v_isSharedCheck_2418_ = !lean_is_exclusive(v_code_2000_);
if (v_isSharedCheck_2418_ == 0)
{
lean_object* v_unused_2419_; lean_object* v_unused_2420_; 
v_unused_2419_ = lean_ctor_get(v_code_2000_, 1);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v_code_2000_, 0);
lean_dec(v_unused_2420_);
v___x_2413_ = v_code_2000_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_dec(v_code_2000_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 1, v_a_2038_);
lean_ctor_set(v___x_2413_, 0, v_a_2397_);
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2397_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_a_2038_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
v___y_2402_ = v___x_2416_;
goto v___jp_2401_;
}
}
}
else
{
size_t v___x_2421_; size_t v___x_2422_; uint8_t v___x_2423_; 
v___x_2421_ = lean_ptr_addr(v_decl_2407_);
v___x_2422_ = lean_ptr_addr(v_a_2397_);
v___x_2423_ = lean_usize_dec_eq(v___x_2421_, v___x_2422_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
v_isSharedCheck_2430_ = !lean_is_exclusive(v_code_2000_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; lean_object* v_unused_2432_; 
v_unused_2431_ = lean_ctor_get(v_code_2000_, 1);
lean_dec(v_unused_2431_);
v_unused_2432_ = lean_ctor_get(v_code_2000_, 0);
lean_dec(v_unused_2432_);
v___x_2425_ = v_code_2000_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_dec(v_code_2000_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 1, v_a_2038_);
lean_ctor_set(v___x_2425_, 0, v_a_2397_);
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2397_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v_a_2038_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
v___y_2402_ = v___x_2428_;
goto v___jp_2401_;
}
}
}
else
{
lean_dec(v_a_2397_);
lean_dec(v_a_2038_);
v___y_2402_ = v_code_2000_;
goto v___jp_2401_;
}
}
}
else
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_dec(v_a_2397_);
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v___x_2433_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2434_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2433_);
v___y_2402_ = v___x_2434_;
goto v___jp_2401_;
}
v___jp_2401_:
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2403_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_2394_, v___y_2402_);
lean_dec(v_snd_2394_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2403_);
v___x_2405_ = v___x_2399_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v_snd_2394_);
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v_a_2436_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2396_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2396_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
lean_dec_ref(v_code_2000_);
v_a_2444_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2391_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2391_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
case 13:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
lean_del_object(v___x_2040_);
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
lean_dec(v_a_2033_);
lean_dec_ref(v_code_2000_);
v___x_2452_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1);
v___x_2453_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2452_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
return v___x_2453_;
}
case 14:
{
lean_del_object(v___x_2040_);
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
lean_dec(v_a_2033_);
lean_dec_ref(v_code_2000_);
v___y_2021_ = v_a_2003_;
v___y_2022_ = v_a_2004_;
v___y_2023_ = v_a_2005_;
v___y_2024_ = v_a_2006_;
v___y_2025_ = v_a_2007_;
v___y_2026_ = v_a_2008_;
goto v___jp_2020_;
}
case 15:
{
lean_del_object(v___x_2040_);
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
lean_dec(v_a_2033_);
lean_dec_ref(v_code_2000_);
v___y_2021_ = v_a_2003_;
v___y_2022_ = v_a_2004_;
v___y_2023_ = v_a_2005_;
v___y_2024_ = v_a_2006_;
v___y_2025_ = v_a_2007_;
v___y_2026_ = v_a_2008_;
goto v___jp_2020_;
}
default: 
{
lean_object* v___x_2454_; 
lean_inc(v_value_2042_);
lean_del_object(v___x_2040_);
v___x_2454_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_2034_, v_a_2036_, v_a_2033_, v_value_2042_, v_a_2006_);
if (lean_obj_tag(v___x_2454_) == 0)
{
if (lean_obj_tag(v_code_2000_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2494_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2494_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2494_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v_decl_2459_; lean_object* v_k_2460_; size_t v___x_2461_; size_t v___x_2462_; uint8_t v___x_2463_; 
v_decl_2459_ = lean_ctor_get(v_code_2000_, 0);
v_k_2460_ = lean_ctor_get(v_code_2000_, 1);
v___x_2461_ = lean_ptr_addr(v_k_2460_);
v___x_2462_ = lean_ptr_addr(v_a_2038_);
v___x_2463_ = lean_usize_dec_eq(v___x_2461_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2473_; 
v_isSharedCheck_2473_ = !lean_is_exclusive(v_code_2000_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; lean_object* v_unused_2475_; 
v_unused_2474_ = lean_ctor_get(v_code_2000_, 1);
lean_dec(v_unused_2474_);
v_unused_2475_ = lean_ctor_get(v_code_2000_, 0);
lean_dec(v_unused_2475_);
v___x_2465_ = v_code_2000_;
v_isShared_2466_ = v_isSharedCheck_2473_;
goto v_resetjp_2464_;
}
else
{
lean_dec(v_code_2000_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2473_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 1, v_a_2038_);
lean_ctor_set(v___x_2465_, 0, v_a_2455_);
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2455_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_a_2038_);
v___x_2468_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2470_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2468_);
v___x_2470_ = v___x_2457_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
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
else
{
size_t v___x_2476_; size_t v___x_2477_; uint8_t v___x_2478_; 
v___x_2476_ = lean_ptr_addr(v_decl_2459_);
v___x_2477_ = lean_ptr_addr(v_a_2455_);
v___x_2478_ = lean_usize_dec_eq(v___x_2476_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2488_; 
v_isSharedCheck_2488_ = !lean_is_exclusive(v_code_2000_);
if (v_isSharedCheck_2488_ == 0)
{
lean_object* v_unused_2489_; lean_object* v_unused_2490_; 
v_unused_2489_ = lean_ctor_get(v_code_2000_, 1);
lean_dec(v_unused_2489_);
v_unused_2490_ = lean_ctor_get(v_code_2000_, 0);
lean_dec(v_unused_2490_);
v___x_2480_ = v_code_2000_;
v_isShared_2481_ = v_isSharedCheck_2488_;
goto v_resetjp_2479_;
}
else
{
lean_dec(v_code_2000_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2488_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v_a_2038_);
lean_ctor_set(v___x_2480_, 0, v_a_2455_);
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2455_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_a_2038_);
v___x_2483_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2485_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2483_);
v___x_2485_ = v___x_2457_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2483_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
else
{
lean_object* v___x_2492_; 
lean_dec(v_a_2455_);
lean_dec(v_a_2038_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v_code_2000_);
v___x_2492_ = v___x_2457_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_code_2000_);
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
else
{
lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; 
v_unused_2504_ = lean_ctor_get(v___x_2454_, 0);
lean_dec(v_unused_2504_);
v___x_2496_ = v___x_2454_;
v_isShared_2497_ = v_isSharedCheck_2503_;
goto v_resetjp_2495_;
}
else
{
lean_dec(v___x_2454_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2503_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2498_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2499_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2498_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v___x_2499_);
v___x_2501_ = v___x_2496_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v_a_2505_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2454_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2454_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
v___jp_2043_:
{
lean_object* v___x_2045_; 
v___x_2045_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_2034_, v_a_2036_, v_a_2033_, v_value_2042_, v___y_2044_);
if (lean_obj_tag(v___x_2045_) == 0)
{
if (lean_obj_tag(v_code_2000_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2085_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2085_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2085_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v_decl_2050_; lean_object* v_k_2051_; size_t v___x_2052_; size_t v___x_2053_; uint8_t v___x_2054_; 
v_decl_2050_ = lean_ctor_get(v_code_2000_, 0);
v_k_2051_ = lean_ctor_get(v_code_2000_, 1);
v___x_2052_ = lean_ptr_addr(v_k_2051_);
v___x_2053_ = lean_ptr_addr(v_a_2038_);
v___x_2054_ = lean_usize_dec_eq(v___x_2052_, v___x_2053_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2064_; 
v_isSharedCheck_2064_ = !lean_is_exclusive(v_code_2000_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; lean_object* v_unused_2066_; 
v_unused_2065_ = lean_ctor_get(v_code_2000_, 1);
lean_dec(v_unused_2065_);
v_unused_2066_ = lean_ctor_get(v_code_2000_, 0);
lean_dec(v_unused_2066_);
v___x_2056_ = v_code_2000_;
v_isShared_2057_ = v_isSharedCheck_2064_;
goto v_resetjp_2055_;
}
else
{
lean_dec(v_code_2000_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2064_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 1, v_a_2038_);
lean_ctor_set(v___x_2056_, 0, v_a_2046_);
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2046_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_a_2038_);
v___x_2059_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2061_; 
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2059_);
v___x_2061_ = v___x_2048_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
size_t v___x_2067_; size_t v___x_2068_; uint8_t v___x_2069_; 
v___x_2067_ = lean_ptr_addr(v_decl_2050_);
v___x_2068_ = lean_ptr_addr(v_a_2046_);
v___x_2069_ = lean_usize_dec_eq(v___x_2067_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2079_; 
v_isSharedCheck_2079_ = !lean_is_exclusive(v_code_2000_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; lean_object* v_unused_2081_; 
v_unused_2080_ = lean_ctor_get(v_code_2000_, 1);
lean_dec(v_unused_2080_);
v_unused_2081_ = lean_ctor_get(v_code_2000_, 0);
lean_dec(v_unused_2081_);
v___x_2071_ = v_code_2000_;
v_isShared_2072_ = v_isSharedCheck_2079_;
goto v_resetjp_2070_;
}
else
{
lean_dec(v_code_2000_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2079_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v_a_2038_);
lean_ctor_set(v___x_2071_, 0, v_a_2046_);
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2046_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_a_2038_);
v___x_2074_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2076_; 
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2074_);
v___x_2076_ = v___x_2048_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v___x_2083_; 
lean_dec(v_a_2046_);
lean_dec(v_a_2038_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v_code_2000_);
v___x_2083_ = v___x_2048_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_code_2000_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
else
{
lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; 
v_unused_2095_ = lean_ctor_get(v___x_2045_, 0);
lean_dec(v_unused_2095_);
v___x_2087_ = v___x_2045_;
v_isShared_2088_ = v_isSharedCheck_2094_;
goto v_resetjp_2086_;
}
else
{
lean_dec(v___x_2045_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2094_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2089_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2090_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2089_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2090_);
v___x_2092_ = v___x_2087_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2000_);
v_a_2096_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2045_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2045_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2036_);
lean_dec(v_a_2033_);
lean_dec_ref(v_code_2000_);
return v___x_2037_;
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v_a_2033_);
lean_dec_ref(v_k_2002_);
lean_dec_ref(v_code_2000_);
v_a_2514_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2035_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2035_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v_value_2030_);
lean_dec_ref(v_k_2002_);
lean_dec_ref(v_decl_2001_);
lean_dec_ref(v_code_2000_);
v_a_2522_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2032_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2032_);
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
v___jp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___y_2011_, v___y_2012_);
lean_dec_ref(v___y_2011_);
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
return v___x_2014_;
}
v___jp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___y_2016_, v___y_2017_);
lean_dec_ref(v___y_2016_);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
return v___x_2019_;
}
v___jp_2020_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1);
v___x_2028_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2027_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
return v___x_2028_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_2000_ = stack[0].m_obj;
lean_object* v_decl_2001_ = stack[1].m_obj;
lean_object* v_k_2002_ = stack[2].m_obj;
lean_object* v_a_2003_ = stack[3].m_obj;
lean_object* v_a_2004_ = stack[4].m_obj;
lean_object* v_a_2005_ = stack[5].m_obj;
lean_object* v_a_2006_ = stack[6].m_obj;
lean_object* v_a_2007_ = stack[7].m_obj;
lean_object* v_a_2008_ = stack[8].m_obj;
lean_object* v_res_2530_;
v_res_2530_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(v_code_2000_, v_decl_2001_, v_k_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
stack->m_obj
 = v_res_2530_;
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2532_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_2533_ = lean_unsigned_to_nat(44u);
v___x_2534_ = lean_unsigned_to_nat(284u);
v___x_2535_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0));
v___x_2536_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_2537_ = l_mkPanicMessageWithDecl(v___x_2536_, v___x_2535_, v___x_2534_, v___x_2533_, v___x_2532_);
return v___x_2537_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2538_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_2539_ = lean_unsigned_to_nat(59u);
v___x_2540_ = lean_unsigned_to_nat(287u);
v___x_2541_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0));
v___x_2542_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_2543_ = l_mkPanicMessageWithDecl(v___x_2542_, v___x_2541_, v___x_2540_, v___x_2539_, v___x_2538_);
return v___x_2543_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(lean_object* v_code_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
switch(lean_obj_tag(v_code_2544_))
{
case 0:
{
lean_object* v_decl_2552_; lean_object* v_k_2553_; lean_object* v___x_2554_; 
v_decl_2552_ = lean_ctor_get(v_code_2544_, 0);
lean_inc_ref(v_decl_2552_);
v_k_2553_ = lean_ctor_get(v_code_2544_, 1);
lean_inc_ref(v_k_2553_);
v___x_2554_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(v_code_2544_, v_decl_2552_, v_k_2553_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2554_;
}
case 2:
{
lean_object* v_decl_2555_; lean_object* v_k_2556_; lean_object* v_params_2557_; lean_object* v_value_2558_; uint8_t v___x_2559_; lean_object* v___x_2560_; 
v_decl_2555_ = lean_ctor_get(v_code_2544_, 0);
v_k_2556_ = lean_ctor_get(v_code_2544_, 1);
v_params_2557_ = lean_ctor_get(v_decl_2555_, 2);
v_value_2558_ = lean_ctor_get(v_decl_2555_, 4);
v___x_2559_ = 1;
lean_inc_ref(v_value_2558_);
v___x_2560_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_value_2558_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v_currDeclResultType_2562_; lean_object* v___x_2563_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v___x_2560_, 1);
v_currDeclResultType_2562_ = lean_ctor_get(v_a_2545_, 1);
lean_inc_ref(v_params_2557_);
lean_inc_ref(v_currDeclResultType_2562_);
lean_inc_ref(v_decl_2555_);
v___x_2563_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2559_, v_decl_2555_, v_currDeclResultType_2562_, v_params_2557_, v_a_2561_, v_a_2548_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2565_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
lean_inc_ref(v_k_2556_);
v___x_2565_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2556_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2603_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2603_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2603_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
size_t v___x_2570_; size_t v___x_2571_; uint8_t v___x_2572_; 
v___x_2570_ = lean_ptr_addr(v_k_2556_);
v___x_2571_ = lean_ptr_addr(v_a_2566_);
v___x_2572_ = lean_usize_dec_eq(v___x_2570_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2582_; 
v_isSharedCheck_2582_ = !lean_is_exclusive(v_code_2544_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; lean_object* v_unused_2584_; 
v_unused_2583_ = lean_ctor_get(v_code_2544_, 1);
lean_dec(v_unused_2583_);
v_unused_2584_ = lean_ctor_get(v_code_2544_, 0);
lean_dec(v_unused_2584_);
v___x_2574_ = v_code_2544_;
v_isShared_2575_ = v_isSharedCheck_2582_;
goto v_resetjp_2573_;
}
else
{
lean_dec(v_code_2544_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2582_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 1, v_a_2566_);
lean_ctor_set(v___x_2574_, 0, v_a_2564_);
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2564_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_a_2566_);
v___x_2577_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2577_);
v___x_2579_ = v___x_2568_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
size_t v___x_2585_; size_t v___x_2586_; uint8_t v___x_2587_; 
v___x_2585_ = lean_ptr_addr(v_decl_2555_);
v___x_2586_ = lean_ptr_addr(v_a_2564_);
v___x_2587_ = lean_usize_dec_eq(v___x_2585_, v___x_2586_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2597_; 
v_isSharedCheck_2597_ = !lean_is_exclusive(v_code_2544_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; lean_object* v_unused_2599_; 
v_unused_2598_ = lean_ctor_get(v_code_2544_, 1);
lean_dec(v_unused_2598_);
v_unused_2599_ = lean_ctor_get(v_code_2544_, 0);
lean_dec(v_unused_2599_);
v___x_2589_ = v_code_2544_;
v_isShared_2590_ = v_isSharedCheck_2597_;
goto v_resetjp_2588_;
}
else
{
lean_dec(v_code_2544_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2597_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 1, v_a_2566_);
lean_ctor_set(v___x_2589_, 0, v_a_2564_);
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2564_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_a_2566_);
v___x_2592_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2594_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2592_);
v___x_2594_ = v___x_2568_;
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
}
else
{
lean_object* v___x_2601_; 
lean_dec(v_a_2566_);
lean_dec(v_a_2564_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v_code_2544_);
v___x_2601_ = v___x_2568_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_code_2544_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
else
{
lean_dec(v_a_2564_);
lean_dec_ref_known(v_code_2544_, 2);
return v___x_2565_;
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref_known(v_code_2544_, 2);
v_a_2604_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2563_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2563_);
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
lean_dec_ref_known(v_code_2544_, 2);
return v___x_2560_;
}
}
case 3:
{
lean_object* v_fvarId_2612_; lean_object* v_args_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; 
v_fvarId_2612_ = lean_ctor_get(v_code_2544_, 0);
v_args_2613_ = lean_ctor_get(v_code_2544_, 1);
v___x_2614_ = 1;
v___x_2615_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_2614_, v_fvarId_2612_, v_a_2548_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v___x_2615_, 1);
if (lean_obj_tag(v_a_2616_) == 1)
{
lean_object* v_val_2617_; lean_object* v_params_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; 
v_val_2617_ = lean_ctor_get(v_a_2616_, 0);
lean_inc(v_val_2617_);
lean_dec_ref_known(v_a_2616_, 1);
v_params_2618_ = lean_ctor_get(v_val_2617_, 2);
lean_inc_ref(v_params_2618_);
lean_dec(v_val_2617_);
v___f_2619_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2619_, 0, v_params_2618_);
v___x_2620_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2613_, v___f_2619_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2648_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2648_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2648_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v_fst_2625_; lean_object* v_snd_2626_; lean_object* v___y_2628_; uint8_t v___y_2634_; uint8_t v___x_2644_; 
v_fst_2625_ = lean_ctor_get(v_a_2621_, 0);
lean_inc(v_fst_2625_);
v_snd_2626_ = lean_ctor_get(v_a_2621_, 1);
lean_inc(v_snd_2626_);
lean_dec(v_a_2621_);
v___x_2644_ = l_Lean_instBEqFVarId_beq(v_fvarId_2612_, v_fvarId_2612_);
if (v___x_2644_ == 0)
{
v___y_2634_ = v___x_2644_;
goto v___jp_2633_;
}
else
{
size_t v___x_2645_; size_t v___x_2646_; uint8_t v___x_2647_; 
v___x_2645_ = lean_ptr_addr(v_args_2613_);
v___x_2646_ = lean_ptr_addr(v_fst_2625_);
v___x_2647_ = lean_usize_dec_eq(v___x_2645_, v___x_2646_);
v___y_2634_ = v___x_2647_;
goto v___jp_2633_;
}
v___jp_2627_:
{
lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2629_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_2626_, v___y_2628_);
lean_dec(v_snd_2626_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2629_);
v___x_2631_ = v___x_2623_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2629_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
v___jp_2633_:
{
if (v___y_2634_ == 0)
{
lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_inc(v_fvarId_2612_);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_code_2544_);
if (v_isSharedCheck_2641_ == 0)
{
lean_object* v_unused_2642_; lean_object* v_unused_2643_; 
v_unused_2642_ = lean_ctor_get(v_code_2544_, 1);
lean_dec(v_unused_2642_);
v_unused_2643_ = lean_ctor_get(v_code_2544_, 0);
lean_dec(v_unused_2643_);
v___x_2636_ = v_code_2544_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_dec(v_code_2544_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 1, v_fst_2625_);
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_fvarId_2612_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_fst_2625_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
v___y_2628_ = v___x_2639_;
goto v___jp_2627_;
}
}
}
else
{
lean_dec(v_fst_2625_);
v___y_2628_ = v_code_2544_;
goto v___jp_2627_;
}
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec_ref_known(v_code_2544_, 2);
v_a_2649_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2620_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2620_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
lean_dec(v_a_2616_);
lean_dec_ref_known(v_code_2544_, 2);
v___x_2657_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1);
v___x_2658_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2657_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2658_;
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec_ref_known(v_code_2544_, 2);
v_a_2659_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2615_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2615_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
case 4:
{
lean_object* v_cases_2667_; lean_object* v_typeName_2668_; lean_object* v_resultType_2669_; lean_object* v_discr_2670_; lean_object* v_alts_2671_; uint8_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_cases_2667_ = lean_ctor_get(v_code_2544_, 0);
v_typeName_2668_ = lean_ctor_get(v_cases_2667_, 0);
lean_inc(v_typeName_2668_);
v_resultType_2669_ = lean_ctor_get(v_cases_2667_, 1);
lean_inc_ref(v_resultType_2669_);
v_discr_2670_ = lean_ctor_get(v_cases_2667_, 2);
lean_inc(v_discr_2670_);
v_alts_2671_ = lean_ctor_get(v_cases_2667_, 3);
lean_inc_ref_n(v_alts_2671_, 2);
v___x_2672_ = 1;
v___x_2673_ = lean_unsigned_to_nat(0u);
v___x_2674_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(v___x_2673_, v_alts_2671_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2674_, 1);
v___x_2676_ = lean_box(0);
lean_inc(v_typeName_2668_);
v___x_2677_ = l_Lean_mkConst(v_typeName_2668_, v___x_2676_);
lean_inc(v_discr_2670_);
v___x_2678_ = l_Lean_Compiler_LCNF_getType(v_discr_2670_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; uint8_t v___x_2680_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2680_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2679_, v___x_2677_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; 
lean_inc_ref(v___x_2677_);
lean_inc(v_discr_2670_);
v___x_2681_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_discr_2670_, v_a_2679_, v___x_2677_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2681_, 1);
v___x_2683_ = lean_box(0);
v___x_2684_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2672_, v___x_2683_, v___x_2677_, v_a_2682_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v_fvarId_2686_; lean_object* v___x_2687_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
v_fvarId_2686_ = lean_ctor_get(v_a_2685_, 0);
lean_inc(v_fvarId_2686_);
v___x_2687_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_2668_, v_a_2675_, v_alts_2671_, v_resultType_2669_, v_discr_2670_, v_code_2544_, v_fvarId_2686_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec(v_discr_2670_);
lean_dec_ref(v_resultType_2669_);
lean_dec_ref(v_alts_2671_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2696_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2690_ = v___x_2687_;
v_isShared_2691_ = v_isSharedCheck_2696_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2687_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2696_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2692_, 0, v_a_2685_);
lean_ctor_set(v___x_2692_, 1, v_a_2688_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2692_);
v___x_2694_ = v___x_2690_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
else
{
lean_dec(v_a_2685_);
return v___x_2687_;
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec(v_a_2675_);
lean_dec_ref(v_alts_2671_);
lean_dec(v_discr_2670_);
lean_dec_ref(v_resultType_2669_);
lean_dec(v_typeName_2668_);
lean_dec_ref_known(v_code_2544_, 1);
v_a_2697_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2684_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2684_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec_ref(v___x_2677_);
lean_dec(v_a_2675_);
lean_dec_ref(v_alts_2671_);
lean_dec(v_discr_2670_);
lean_dec_ref(v_resultType_2669_);
lean_dec(v_typeName_2668_);
lean_dec_ref_known(v_code_2544_, 1);
v_a_2705_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2681_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2681_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
else
{
lean_object* v___x_2713_; 
lean_dec(v_a_2679_);
lean_dec_ref(v___x_2677_);
lean_inc(v_discr_2670_);
v___x_2713_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_2668_, v_a_2675_, v_alts_2671_, v_resultType_2669_, v_discr_2670_, v_code_2544_, v_discr_2670_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec(v_discr_2670_);
lean_dec_ref(v_resultType_2669_);
lean_dec_ref(v_alts_2671_);
return v___x_2713_;
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec_ref(v___x_2677_);
lean_dec(v_a_2675_);
lean_dec_ref(v_alts_2671_);
lean_dec(v_discr_2670_);
lean_dec_ref(v_resultType_2669_);
lean_dec(v_typeName_2668_);
lean_dec_ref_known(v_code_2544_, 1);
v_a_2714_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2678_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2678_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec_ref(v_alts_2671_);
lean_dec(v_discr_2670_);
lean_dec_ref(v_resultType_2669_);
lean_dec(v_typeName_2668_);
lean_dec_ref_known(v_code_2544_, 1);
v_a_2722_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2674_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2674_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_2730_; lean_object* v_currDeclResultType_2731_; lean_object* v___x_2732_; 
v_fvarId_2730_ = lean_ctor_get(v_code_2544_, 0);
lean_inc_n(v_fvarId_2730_, 2);
v_currDeclResultType_2731_ = lean_ctor_get(v_a_2545_, 1);
v___x_2732_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2730_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; uint8_t v___x_2734_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2733_, v_currDeclResultType_2731_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; 
lean_inc_ref(v_currDeclResultType_2731_);
lean_inc(v_fvarId_2730_);
v___x_2735_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_2730_, v_a_2733_, v_currDeclResultType_2731_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; uint8_t v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2737_ = 1;
v___x_2738_ = lean_box(0);
lean_inc_ref(v_currDeclResultType_2731_);
v___x_2739_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2737_, v___x_2738_, v_currDeclResultType_2731_, v_a_2736_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v_fvarId_2741_; lean_object* v___x_2742_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2739_, 1);
v_fvarId_2741_ = lean_ctor_get(v_a_2740_, 0);
lean_inc(v_fvarId_2741_);
v___x_2742_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_2730_, v_code_2544_, v_fvarId_2741_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec(v_fvarId_2730_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2751_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2751_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2751_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v_a_2740_);
lean_ctor_set(v___x_2747_, 1, v_a_2743_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2747_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
else
{
lean_dec(v_a_2740_);
return v___x_2742_;
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec_ref_known(v_code_2544_, 1);
lean_dec(v_fvarId_2730_);
v_a_2752_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2739_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2739_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec_ref_known(v_code_2544_, 1);
lean_dec(v_fvarId_2730_);
v_a_2760_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2735_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2735_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v___x_2768_; 
lean_dec(v_a_2733_);
lean_inc(v_fvarId_2730_);
v___x_2768_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_2730_, v_code_2544_, v_fvarId_2730_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec(v_fvarId_2730_);
return v___x_2768_;
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec_ref_known(v_code_2544_, 1);
lean_dec(v_fvarId_2730_);
v_a_2769_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2732_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2732_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
case 6:
{
lean_object* v_type_2777_; lean_object* v_currDeclResultType_2778_; size_t v___x_2779_; size_t v___x_2780_; uint8_t v___x_2781_; 
v_type_2777_ = lean_ctor_get(v_code_2544_, 0);
v_currDeclResultType_2778_ = lean_ctor_get(v_a_2545_, 1);
v___x_2779_ = lean_ptr_addr(v_type_2777_);
v___x_2780_ = lean_ptr_addr(v_currDeclResultType_2778_);
v___x_2781_ = lean_usize_dec_eq(v___x_2779_, v___x_2780_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2789_; 
v_isSharedCheck_2789_ = !lean_is_exclusive(v_code_2544_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v_code_2544_, 0);
lean_dec(v_unused_2790_);
v___x_2783_ = v_code_2544_;
v_isShared_2784_ = v_isSharedCheck_2789_;
goto v_resetjp_2782_;
}
else
{
lean_dec(v_code_2544_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2789_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
lean_inc_ref(v_currDeclResultType_2778_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v_currDeclResultType_2778_);
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_currDeclResultType_2778_);
v___x_2786_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
return v___x_2787_;
}
}
}
else
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_code_2544_);
return v___x_2791_;
}
}
case 8:
{
lean_object* v_fvarId_2792_; lean_object* v_i_2793_; lean_object* v_y_2794_; lean_object* v_k_2795_; lean_object* v___x_2796_; 
v_fvarId_2792_ = lean_ctor_get(v_code_2544_, 0);
lean_inc(v_fvarId_2792_);
v_i_2793_ = lean_ctor_get(v_code_2544_, 1);
lean_inc(v_i_2793_);
v_y_2794_ = lean_ctor_get(v_code_2544_, 2);
lean_inc(v_y_2794_);
v_k_2795_ = lean_ctor_get(v_code_2544_, 3);
lean_inc_ref_n(v_k_2795_, 2);
v___x_2796_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2795_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
v___x_2798_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11);
lean_inc(v_y_2794_);
v___x_2799_ = l_Lean_Compiler_LCNF_getType(v_y_2794_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; uint8_t v___x_2801_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2801_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2800_, v___x_2798_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; 
lean_inc(v_y_2794_);
v___x_2802_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_y_2794_, v_a_2800_, v___x_2798_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v___x_2804_ = 1;
v___x_2805_ = lean_box(0);
v___x_2806_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2804_, v___x_2805_, v___x_2798_, v_a_2803_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v_fvarId_2808_; lean_object* v___x_2809_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v_fvarId_2808_ = lean_ctor_get(v_a_2807_, 0);
lean_inc(v_fvarId_2808_);
v___x_2809_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_2792_, v_i_2793_, v_a_2797_, v_y_2794_, v_k_2795_, v_code_2544_, v_fvarId_2808_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec_ref(v_k_2795_);
lean_dec(v_y_2794_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2818_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2812_ = v___x_2809_;
v_isShared_2813_ = v_isSharedCheck_2818_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2818_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; lean_object* v___x_2816_; 
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v_a_2807_);
lean_ctor_set(v___x_2814_, 1, v_a_2810_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 0, v___x_2814_);
v___x_2816_ = v___x_2812_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
else
{
lean_dec(v_a_2807_);
return v___x_2809_;
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v_a_2797_);
lean_dec_ref(v_k_2795_);
lean_dec(v_y_2794_);
lean_dec(v_i_2793_);
lean_dec_ref_known(v_code_2544_, 4);
lean_dec(v_fvarId_2792_);
v_a_2819_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2806_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2806_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
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
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec(v_a_2797_);
lean_dec_ref(v_k_2795_);
lean_dec(v_y_2794_);
lean_dec(v_i_2793_);
lean_dec_ref_known(v_code_2544_, 4);
lean_dec(v_fvarId_2792_);
v_a_2827_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2802_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2802_);
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
}
else
{
lean_object* v___x_2835_; 
lean_dec(v_a_2800_);
lean_inc(v_y_2794_);
v___x_2835_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_2792_, v_i_2793_, v_a_2797_, v_y_2794_, v_k_2795_, v_code_2544_, v_y_2794_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec_ref(v_k_2795_);
lean_dec(v_y_2794_);
return v___x_2835_;
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec(v_a_2797_);
lean_dec_ref(v_k_2795_);
lean_dec(v_y_2794_);
lean_dec(v_i_2793_);
lean_dec_ref_known(v_code_2544_, 4);
lean_dec(v_fvarId_2792_);
v_a_2836_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2799_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2799_);
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
else
{
lean_dec_ref(v_k_2795_);
lean_dec(v_y_2794_);
lean_dec(v_i_2793_);
lean_dec_ref_known(v_code_2544_, 4);
lean_dec(v_fvarId_2792_);
return v___x_2796_;
}
}
case 9:
{
lean_object* v_fvarId_2844_; lean_object* v_i_2845_; lean_object* v_offset_2846_; lean_object* v_y_2847_; lean_object* v_ty_2848_; lean_object* v_k_2849_; lean_object* v___x_2850_; 
v_fvarId_2844_ = lean_ctor_get(v_code_2544_, 0);
lean_inc(v_fvarId_2844_);
v_i_2845_ = lean_ctor_get(v_code_2544_, 1);
lean_inc(v_i_2845_);
v_offset_2846_ = lean_ctor_get(v_code_2544_, 2);
lean_inc(v_offset_2846_);
v_y_2847_ = lean_ctor_get(v_code_2544_, 3);
lean_inc(v_y_2847_);
v_ty_2848_ = lean_ctor_get(v_code_2544_, 4);
lean_inc_ref(v_ty_2848_);
v_k_2849_ = lean_ctor_get(v_code_2544_, 5);
lean_inc_ref_n(v_k_2849_, 2);
v___x_2850_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2849_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
lean_inc(v_y_2847_);
v___x_2852_ = l_Lean_Compiler_LCNF_getType(v_y_2847_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; uint8_t v___x_2854_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2853_, v_ty_2848_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_inc_ref(v_ty_2848_);
lean_inc(v_y_2847_);
v___x_2855_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_y_2847_, v_a_2853_, v_ty_2848_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; uint8_t v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v___x_2857_ = 1;
v___x_2858_ = lean_box(0);
lean_inc_ref(v_ty_2848_);
v___x_2859_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2857_, v___x_2858_, v_ty_2848_, v_a_2856_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v_fvarId_2861_; lean_object* v___x_2862_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
v_fvarId_2861_ = lean_ctor_get(v_a_2860_, 0);
lean_inc(v_fvarId_2861_);
v___x_2862_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_2844_, v_i_2845_, v_offset_2846_, v_ty_2848_, v_a_2851_, v_y_2847_, v_k_2849_, v_code_2544_, v_fvarId_2861_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec_ref(v_k_2849_);
lean_dec(v_y_2847_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2871_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2871_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2871_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2867_, 0, v_a_2860_);
lean_ctor_set(v___x_2867_, 1, v_a_2863_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2867_);
v___x_2869_ = v___x_2865_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
else
{
lean_dec(v_a_2860_);
return v___x_2862_;
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_a_2851_);
lean_dec_ref(v_k_2849_);
lean_dec_ref(v_ty_2848_);
lean_dec(v_y_2847_);
lean_dec(v_offset_2846_);
lean_dec(v_i_2845_);
lean_dec(v_fvarId_2844_);
lean_dec_ref_known(v_code_2544_, 6);
v_a_2872_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2859_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2859_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_a_2851_);
lean_dec_ref(v_k_2849_);
lean_dec_ref(v_ty_2848_);
lean_dec(v_y_2847_);
lean_dec(v_offset_2846_);
lean_dec(v_i_2845_);
lean_dec(v_fvarId_2844_);
lean_dec_ref_known(v_code_2544_, 6);
v_a_2880_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2855_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2855_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v___x_2888_; 
lean_dec(v_a_2853_);
lean_inc(v_y_2847_);
v___x_2888_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_2844_, v_i_2845_, v_offset_2846_, v_ty_2848_, v_a_2851_, v_y_2847_, v_k_2849_, v_code_2544_, v_y_2847_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec_ref(v_k_2849_);
lean_dec(v_y_2847_);
return v___x_2888_;
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec(v_a_2851_);
lean_dec_ref(v_k_2849_);
lean_dec_ref(v_ty_2848_);
lean_dec(v_y_2847_);
lean_dec(v_offset_2846_);
lean_dec(v_i_2845_);
lean_dec(v_fvarId_2844_);
lean_dec_ref_known(v_code_2544_, 6);
v_a_2889_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2852_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2852_);
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
else
{
lean_dec_ref(v_k_2849_);
lean_dec_ref(v_ty_2848_);
lean_dec(v_y_2847_);
lean_dec(v_offset_2846_);
lean_dec(v_i_2845_);
lean_dec(v_fvarId_2844_);
lean_dec_ref_known(v_code_2544_, 6);
return v___x_2850_;
}
}
default: 
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
lean_dec_ref(v_code_2544_);
v___x_2897_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2);
v___x_2898_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2897_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2898_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_2544_ = stack[0].m_obj;
lean_object* v_a_2545_ = stack[1].m_obj;
lean_object* v_a_2546_ = stack[2].m_obj;
lean_object* v_a_2547_ = stack[3].m_obj;
lean_object* v_a_2548_ = stack[4].m_obj;
lean_object* v_a_2549_ = stack[5].m_obj;
lean_object* v_a_2550_ = stack[6].m_obj;
lean_object* v_res_2899_;
v_res_2899_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_code_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
stack->m_obj
 = v_res_2899_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed(lean_object* v_code_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_code_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
return v_res_2908_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(lean_object* v_i_2909_, lean_object* v_as_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = lean_array_get_size(v_as_2910_);
v___x_2919_ = lean_nat_dec_lt(v_i_2909_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; 
lean_dec(v_i_2909_);
v___x_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2920_, 0, v_as_2910_);
return v___x_2920_;
}
else
{
lean_object* v___f_2921_; lean_object* v_a_2922_; lean_object* v___x_2923_; 
v___f_2921_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed), 8, 0);
v_a_2922_ = lean_array_fget_borrowed(v_as_2910_, v_i_2909_);
lean_inc(v_a_2922_);
v___x_2923_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_a_2922_, v___f_2921_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; size_t v___x_2925_; size_t v___x_2926_; uint8_t v___x_2927_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2923_, 1);
v___x_2925_ = lean_ptr_addr(v_a_2922_);
v___x_2926_ = lean_ptr_addr(v_a_2924_);
v___x_2927_ = lean_usize_dec_eq(v___x_2925_, v___x_2926_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = lean_unsigned_to_nat(1u);
v___x_2929_ = lean_nat_add(v_i_2909_, v___x_2928_);
v___x_2930_ = lean_array_fset(v_as_2910_, v_i_2909_, v_a_2924_);
lean_dec(v_i_2909_);
v_i_2909_ = v___x_2929_;
v_as_2910_ = v___x_2930_;
goto _start;
}
else
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_dec(v_a_2924_);
v___x_2932_ = lean_unsigned_to_nat(1u);
v___x_2933_ = lean_nat_add(v_i_2909_, v___x_2932_);
lean_dec(v_i_2909_);
v_i_2909_ = v___x_2933_;
goto _start;
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec_ref(v_as_2910_);
lean_dec(v_i_2909_);
v_a_2935_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2923_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2923_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_2909_ = stack[0].m_obj;
lean_object* v_as_2910_ = stack[1].m_obj;
lean_object* v___y_2911_ = stack[2].m_obj;
lean_object* v___y_2912_ = stack[3].m_obj;
lean_object* v___y_2913_ = stack[4].m_obj;
lean_object* v___y_2914_ = stack[5].m_obj;
lean_object* v___y_2915_ = stack[6].m_obj;
lean_object* v___y_2916_ = stack[7].m_obj;
lean_object* v_res_2943_;
v_res_2943_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(v_i_2909_, v_as_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
stack->m_obj
 = v_res_2943_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3___boxed(lean_object* v_i_2944_, lean_object* v_as_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(v_i_2944_, v_as_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___boxed(lean_object* v_code_2954_, lean_object* v_decl_2955_, lean_object* v_k_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(v_code_2954_, v_decl_2955_, v_k_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
return v_res_2964_;
}
}
lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(uint8_t v_pu_2965_, lean_object* v_alt_2966_, lean_object* v_f_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_alt_2966_, v_f_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
return v___x_2975_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2965_ = stack[0].m_num;
lean_object* v_alt_2966_ = stack[1].m_obj;
lean_object* v_f_2967_ = stack[2].m_obj;
lean_object* v___y_2968_ = stack[3].m_obj;
lean_object* v___y_2969_ = stack[4].m_obj;
lean_object* v___y_2970_ = stack[5].m_obj;
lean_object* v___y_2971_ = stack[6].m_obj;
lean_object* v___y_2972_ = stack[7].m_obj;
lean_object* v___y_2973_ = stack[8].m_obj;
lean_object* v_res_2976_;
v_res_2976_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(v_pu_2965_, v_alt_2966_, v_f_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
stack->m_obj
 = v_res_2976_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___boxed(lean_object* v_pu_2977_, lean_object* v_alt_2978_, lean_object* v_f_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
uint8_t v_pu_boxed_2987_; lean_object* v_res_2988_; 
v_pu_boxed_2987_ = lean_unbox(v_pu_2977_);
v_res_2988_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(v_pu_boxed_2987_, v_alt_2978_, v_f_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
return v_res_2988_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(lean_object* v_as_2992_, size_t v_i_2993_, size_t v_stop_2994_, lean_object* v_b_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v_a_3002_; uint8_t v___x_3006_; 
v___x_3006_ = lean_usize_dec_eq(v_i_2993_, v_stop_2994_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v_value_3008_; 
v___x_3007_ = lean_array_uget(v_as_2992_, v_i_2993_);
v_value_3008_ = lean_ctor_get(v___x_3007_, 1);
lean_inc_ref(v_value_3008_);
if (lean_obj_tag(v_value_3008_) == 0)
{
lean_object* v_toSignature_3009_; uint8_t v_recursive_3010_; lean_object* v_inlineAttr_x3f_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3056_; 
v_toSignature_3009_ = lean_ctor_get(v___x_3007_, 0);
v_recursive_3010_ = lean_ctor_get_uint8(v___x_3007_, sizeof(void*)*3);
v_inlineAttr_x3f_3011_ = lean_ctor_get(v___x_3007_, 2);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v___x_3007_, 1);
lean_dec(v_unused_3057_);
v___x_3013_ = v___x_3007_;
v_isShared_3014_ = v_isSharedCheck_3056_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_inlineAttr_x3f_3011_);
lean_inc(v_toSignature_3009_);
lean_dec(v___x_3007_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3056_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v_code_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3055_; 
v_code_3015_ = lean_ctor_get(v_value_3008_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v_value_3008_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3017_ = v_value_3008_;
v_isShared_3018_ = v_isSharedCheck_3055_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_code_3015_);
lean_dec(v_value_3008_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3055_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v_name_3019_; lean_object* v_type_3020_; lean_object* v_s_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_name_3019_ = lean_ctor_get(v_toSignature_3009_, 0);
v_type_3020_ = lean_ctor_get(v_toSignature_3009_, 2);
lean_inc_ref(v_type_3020_);
lean_inc(v_name_3019_);
v_s_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_3021_, 0, v_name_3019_);
lean_ctor_set(v_s_3021_, 1, v_type_3020_);
v___x_3022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0));
v___x_3023_ = lean_st_mk_ref(v___x_3022_);
v___x_3024_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_code_3015_, v_s_3021_, v___x_3023_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec_ref_known(v_s_3021_, 2);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; lean_object* v_auxDecls_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; lean_object* v___x_3031_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v___x_3026_ = lean_st_ref_get(v___x_3023_);
lean_dec(v___x_3023_);
v_auxDecls_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc_ref(v_auxDecls_3027_);
lean_dec(v___x_3026_);
v___x_3028_ = l_Array_append___redArg(v_b_2995_, v_auxDecls_3027_);
lean_dec_ref(v_auxDecls_3027_);
v___x_3029_ = 1;
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v_a_3025_);
v___x_3031_ = v___x_3017_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3025_);
v___x_3031_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3033_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 1, v___x_3031_);
v___x_3033_ = v___x_3013_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_toSignature_3009_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3045_, 2, v_inlineAttr_x3f_3011_);
lean_ctor_set_uint8(v_reuseFailAlloc_3045_, sizeof(void*)*3, v_recursive_3010_);
v___x_3033_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_3029_, v___x_3033_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3036_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v___x_3034_, 1);
v___x_3036_ = lean_array_push(v___x_3028_, v_a_3035_);
v_a_3002_ = v___x_3036_;
goto v___jp_3001_;
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref(v___x_3028_);
v_a_3037_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3034_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3034_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec(v___x_3023_);
lean_del_object(v___x_3017_);
lean_del_object(v___x_3013_);
lean_dec(v_inlineAttr_x3f_3011_);
lean_dec_ref(v_toSignature_3009_);
lean_dec_ref(v_b_2995_);
v_a_3047_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3024_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3024_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
}
else
{
lean_object* v___x_3058_; 
lean_dec_ref_known(v_value_3008_, 1);
v___x_3058_ = lean_array_push(v_b_2995_, v___x_3007_);
v_a_3002_ = v___x_3058_;
goto v___jp_3001_;
}
}
else
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3059_, 0, v_b_2995_);
return v___x_3059_;
}
v___jp_3001_:
{
size_t v___x_3003_; size_t v___x_3004_; 
v___x_3003_ = ((size_t)1ULL);
v___x_3004_ = lean_usize_add(v_i_2993_, v___x_3003_);
v_i_2993_ = v___x_3004_;
v_b_2995_ = v_a_3002_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2992_ = stack[0].m_obj;
size_t v_i_2993_ = stack[1].m_num;
size_t v_stop_2994_ = stack[2].m_num;
lean_object* v_b_2995_ = stack[3].m_obj;
lean_object* v___y_2996_ = stack[4].m_obj;
lean_object* v___y_2997_ = stack[5].m_obj;
lean_object* v___y_2998_ = stack[6].m_obj;
lean_object* v___y_2999_ = stack[7].m_obj;
lean_object* v_res_3060_;
v_res_3060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_as_2992_, v_i_2993_, v_stop_2994_, v_b_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
stack->m_obj
 = v_res_3060_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___boxed(lean_object* v_as_3061_, lean_object* v_i_3062_, lean_object* v_stop_3063_, lean_object* v_b_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
size_t v_i_boxed_3070_; size_t v_stop_boxed_3071_; lean_object* v_res_3072_; 
v_i_boxed_3070_ = lean_unbox_usize(v_i_3062_);
lean_dec(v_i_3062_);
v_stop_boxed_3071_ = lean_unbox_usize(v_stop_3063_);
lean_dec(v_stop_3063_);
v_res_3072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_as_3061_, v_i_boxed_3070_, v_stop_boxed_3071_, v_b_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec_ref(v_as_3061_);
return v_res_3072_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(lean_object* v_decls_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v___y_3080_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3083_ = lean_unsigned_to_nat(0u);
v___x_3084_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0));
v___x_3085_ = lean_array_get_size(v_decls_3073_);
v___x_3086_ = lean_nat_dec_lt(v___x_3083_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Lean_Compiler_LCNF_addBoxedVersions(v___x_3084_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
return v___x_3087_;
}
else
{
uint8_t v___x_3088_; 
v___x_3088_ = lean_nat_dec_le(v___x_3085_, v___x_3085_);
if (v___x_3088_ == 0)
{
if (v___x_3086_ == 0)
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lean_Compiler_LCNF_addBoxedVersions(v___x_3084_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
return v___x_3089_;
}
else
{
size_t v___x_3090_; size_t v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = ((size_t)0ULL);
v___x_3091_ = lean_usize_of_nat(v___x_3085_);
v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_decls_3073_, v___x_3090_, v___x_3091_, v___x_3084_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
v___y_3080_ = v___x_3092_;
goto v___jp_3079_;
}
}
else
{
size_t v___x_3093_; size_t v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = ((size_t)0ULL);
v___x_3094_ = lean_usize_of_nat(v___x_3085_);
v___x_3095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_decls_3073_, v___x_3093_, v___x_3094_, v___x_3084_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
v___y_3080_ = v___x_3095_;
goto v___jp_3079_;
}
}
v___jp_3079_:
{
if (lean_obj_tag(v___y_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3082_; 
v_a_3081_ = lean_ctor_get(v___y_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___y_3080_, 1);
v___x_3082_ = l_Lean_Compiler_LCNF_addBoxedVersions(v_a_3081_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
return v___x_3082_;
}
else
{
return v___y_3080_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_3073_ = stack[0].m_obj;
lean_object* v_a_3074_ = stack[1].m_obj;
lean_object* v_a_3075_ = stack[2].m_obj;
lean_object* v_a_3076_ = stack[3].m_obj;
lean_object* v_a_3077_ = stack[4].m_obj;
lean_object* v_res_3096_;
v_res_3096_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(v_decls_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
stack->m_obj
 = v_res_3096_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run___boxed(lean_object* v_decls_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(v_decls_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec_ref(v_decls_3097_);
return v_res_3103_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3185_; uint8_t v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3185_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_));
v___x_3186_ = 1;
v___x_3187_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_));
v___x_3188_ = l_Lean_registerTraceClass(v___x_3185_, v___x_3186_, v___x_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3189_;
v_res_3189_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3189_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2____boxed(lean_object* v_a_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_();
return v_res_3191_;
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
