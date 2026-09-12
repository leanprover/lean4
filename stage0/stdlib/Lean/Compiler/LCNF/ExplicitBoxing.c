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
lean_object* v_name_28_; lean_object* v_type_29_; lean_object* v_params_30_; lean_object* v___x_31_; lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v_name_28_ = lean_ctor_get(v_sig_25_, 0);
lean_inc(v_name_28_);
v_type_29_ = lean_ctor_get(v_sig_25_, 2);
lean_inc_ref(v_type_29_);
v_params_30_ = lean_ctor_get(v_sig_25_, 3);
lean_inc_ref(v_params_30_);
lean_dec_ref(v_sig_25_);
v___x_31_ = lean_st_ref_get(v_a_26_);
v___x_38_ = lean_unsigned_to_nat(0u);
v___x_39_ = lean_array_get_size(v_params_30_);
v___x_40_ = lean_nat_dec_lt(v___x_38_, v___x_39_);
if (v___x_40_ == 0)
{
lean_dec(v___x_31_);
lean_dec_ref(v_type_29_);
lean_dec(v_name_28_);
goto v___jp_32_;
}
else
{
lean_object* v_env_41_; uint8_t v___y_47_; uint8_t v___x_50_; 
v_env_41_ = lean_ctor_get(v___x_31_, 0);
lean_inc_ref(v_env_41_);
lean_dec(v___x_31_);
v___x_50_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_29_);
lean_dec_ref(v_type_29_);
if (v___x_50_ == 0)
{
if (v___x_40_ == 0)
{
goto v___jp_42_;
}
else
{
if (v___x_40_ == 0)
{
goto v___jp_42_;
}
else
{
size_t v___x_51_; size_t v___x_52_; uint8_t v___x_53_; 
v___x_51_ = ((size_t)0ULL);
v___x_52_ = lean_usize_of_nat(v___x_39_);
v___x_53_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(v_params_30_, v___x_51_, v___x_52_);
v___y_47_ = v___x_53_;
goto v___jp_46_;
}
}
}
else
{
v___y_47_ = v___x_50_;
goto v___jp_46_;
}
v___jp_42_:
{
uint8_t v___x_43_; 
v___x_43_ = l_Lean_isExtern(v_env_41_, v_name_28_);
if (v___x_43_ == 0)
{
goto v___jp_32_;
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; 
lean_dec_ref(v_params_30_);
v___x_44_ = lean_box(v___x_43_);
v___x_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
return v___x_45_;
}
}
v___jp_46_:
{
if (v___y_47_ == 0)
{
goto v___jp_42_;
}
else
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec_ref(v_env_41_);
lean_dec_ref(v_params_30_);
lean_dec(v_name_28_);
v___x_48_ = lean_box(v___y_47_);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
}
v___jp_32_:
{
lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_33_ = l_Lean_closureMaxArgs;
v___x_34_ = lean_array_get_size(v_params_30_);
lean_dec_ref(v_params_30_);
v___x_35_ = lean_nat_dec_lt(v___x_33_, v___x_34_);
v___x_36_ = lean_box(v___x_35_);
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
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
lean_object* v_v_82_; lean_object* v_binderName_83_; lean_object* v_type_84_; lean_object* v___x_85_; lean_object* v_bs_x27_86_; uint8_t v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; 
v_v_82_ = lean_array_uget_borrowed(v_bs_74_, v_i_73_);
v_binderName_83_ = lean_ctor_get(v_v_82_, 1);
lean_inc(v_binderName_83_);
v_type_84_ = lean_ctor_get(v_v_82_, 2);
lean_inc_ref(v_type_84_);
v___x_85_ = lean_unsigned_to_nat(0u);
v_bs_x27_86_ = lean_array_uset(v_bs_74_, v_i_73_, v___x_85_);
v___x_87_ = 1;
v___x_88_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_84_);
lean_dec_ref(v_type_84_);
v___x_89_ = 0;
v___x_90_ = l_Lean_Compiler_LCNF_mkParam(v___x_87_, v_binderName_83_, v___x_88_, v___x_89_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; size_t v___x_92_; size_t v___x_93_; lean_object* v___x_94_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
lean_dec_ref_known(v___x_90_, 1);
v___x_92_ = ((size_t)1ULL);
v___x_93_ = lean_usize_add(v_i_73_, v___x_92_);
v___x_94_ = lean_array_uset(v_bs_x27_86_, v_i_73_, v_a_91_);
v_i_73_ = v___x_93_;
v_bs_74_ = v___x_94_;
goto _start;
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec_ref(v_bs_x27_86_);
v_a_96_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_90_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_90_);
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
lean_dec_ref_known(v___x_179_, 1);
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
lean_inc_n(v_a_244_, 2);
lean_dec_ref_known(v___x_243_, 1);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0));
v___x_278_ = lean_array_get_size(v_params_237_);
v___x_279_ = lean_mk_empty_array_with_capacity(v___x_278_);
v___x_280_ = lean_array_get_size(v_a_244_);
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
lean_dec_ref_known(v___x_284_, 1);
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
lean_inc_n(v_a_300_, 2);
lean_dec_ref_known(v___x_299_, 1);
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
v___x_306_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___x_302_, v___x_305_);
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
lean_dec_ref_known(v___x_312_, 1);
v_fvarId_314_ = lean_ctor_get(v_a_313_, 0);
lean_inc(v_fvarId_314_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v_a_313_);
v___x_316_ = lean_array_push(v___x_302_, v___x_315_);
v___x_317_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_317_, 0, v_fvarId_314_);
v___x_318_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___x_316_, v___x_317_);
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
lean_dec_ref_known(v___x_257_, 3);
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
lean_dec_ref_known(v___x_382_, 1);
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
lean_dec_ref_known(v___x_385_, 1);
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
if (v___x_507_ == 0)
{
if (v___x_506_ == 0)
{
uint8_t v___x_508_; 
v___x_508_ = 1;
v___y_501_ = v___x_508_;
goto v___jp_500_;
}
else
{
v___y_505_ = v___x_507_;
goto v___jp_504_;
}
}
else
{
v___y_505_ = v___x_506_;
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
lean_dec_ref_known(v_a_523_, 1);
switch(lean_obj_tag(v_val_524_))
{
case 0:
{
lean_dec_ref_known(v_val_524_, 1);
return v___x_522_;
}
case 9:
{
lean_object* v_args_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_args_525_ = lean_ctor_get(v_val_524_, 1);
lean_inc_ref(v_args_525_);
lean_dec_ref_known(v_val_524_, 2);
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
uint8_t v___x_608_; lean_object* v___x_609_; 
v___x_608_ = 1;
v___x_609_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(v_fvarId_597_, v_fvarIdType_598_, v_a_603_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_735_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_735_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_735_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_735_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
if (lean_obj_tag(v_a_610_) == 0)
{
lean_object* v___x_614_; lean_object* v___x_616_; 
lean_dec_ref(v_expectedType_599_);
v___x_614_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_614_, 0, v_fvarIdType_598_);
lean_ctor_set(v___x_614_, 1, v_fvarId_597_);
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
lean_object* v_val_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_734_; 
lean_del_object(v___x_612_);
lean_dec(v_fvarId_597_);
v_val_618_ = lean_ctor_get(v_a_610_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v_a_610_);
if (v_isSharedCheck_734_ == 0)
{
v___x_620_ = v_a_610_;
v_isShared_621_ = v_isSharedCheck_734_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_val_618_);
lean_dec(v_a_610_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_734_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = 1;
v___x_623_ = lean_box(0);
lean_inc_ref(v_fvarIdType_598_);
v___x_624_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_622_, v___x_623_, v_fvarIdType_598_, v_val_618_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v_fvarId_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v_fvarId_626_ = lean_ctor_get(v_a_625_, 0);
lean_inc(v_fvarId_626_);
v___x_627_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_627_, 0, v_fvarIdType_598_);
lean_ctor_set(v___x_627_, 1, v_fvarId_626_);
lean_inc_ref(v_expectedType_599_);
v___x_628_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_622_, v___x_623_, v_expectedType_599_, v___x_627_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v_fvarId_630_; lean_object* v___x_632_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
v_fvarId_630_ = lean_ctor_get(v_a_629_, 0);
lean_inc(v_fvarId_630_);
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 5);
lean_ctor_set(v___x_620_, 0, v_fvarId_630_);
v___x_632_ = v___x_620_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_fvarId_630_);
v___x_632_ = v_reuseFailAlloc_717_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v_currDecl_636_; lean_object* v_nextAuxIdx_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_715_; 
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v_a_629_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v_a_625_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_st_ref_get(v_a_601_);
v_currDecl_636_ = lean_ctor_get(v_a_600_, 0);
v_nextAuxIdx_637_ = lean_ctor_get(v___x_635_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v___x_635_, 0);
lean_dec(v_unused_716_);
v___x_639_ = v___x_635_;
v_isShared_640_ = v_isSharedCheck_715_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_nextAuxIdx_637_);
lean_dec(v___x_635_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_715_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_641_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__1));
v___x_642_ = lean_name_append_index_after(v___x_641_, v_nextAuxIdx_637_);
lean_inc(v_currDecl_636_);
v___x_643_ = l_Lean_Name_append(v_currDecl_636_, v___x_642_);
v___x_644_ = lean_box(0);
v___x_645_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__2));
lean_inc(v___x_643_);
v___x_646_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_646_, 0, v___x_643_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
lean_ctor_set(v___x_646_, 2, v_expectedType_599_);
lean_ctor_set(v___x_646_, 3, v___x_645_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*4, v___x_608_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_634_);
v___x_648_ = lean_box(0);
v___x_649_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_649_, 0, v___x_646_);
lean_ctor_set(v___x_649_, 1, v___x_647_);
lean_ctor_set(v___x_649_, 2, v___x_648_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*3, v___x_607_);
lean_inc_ref(v___x_649_);
v___x_650_ = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(v___x_622_, v___x_649_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
if (lean_obj_tag(v_a_651_) == 0)
{
lean_object* v___x_652_; lean_object* v_auxDecls_653_; lean_object* v_nextAuxIdx_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_685_; 
v___x_652_ = lean_st_ref_take(v_a_601_);
v_auxDecls_653_ = lean_ctor_get(v___x_652_, 0);
v_nextAuxIdx_654_ = lean_ctor_get(v___x_652_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_685_ == 0)
{
v___x_656_ = v___x_652_;
v_isShared_657_ = v_isSharedCheck_685_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_nextAuxIdx_654_);
lean_inc(v_auxDecls_653_);
lean_dec(v___x_652_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_685_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
lean_inc_ref(v___x_649_);
v___x_658_ = lean_array_push(v_auxDecls_653_, v___x_649_);
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_nat_add(v_nextAuxIdx_654_, v___x_659_);
lean_dec(v_nextAuxIdx_654_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v___x_660_);
lean_ctor_set(v___x_656_, 0, v___x_658_);
v___x_662_ = v___x_656_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v___x_660_);
v___x_662_ = v_reuseFailAlloc_684_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_st_ref_put(v_a_601_, v___x_662_);
v___x_664_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v___x_649_, v_a_605_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_674_; 
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v___x_664_, 0);
lean_dec(v_unused_675_);
v___x_666_ = v___x_664_;
v_isShared_667_ = v_isSharedCheck_674_;
goto v_resetjp_665_;
}
else
{
lean_dec(v___x_664_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_674_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set_tag(v___x_639_, 9);
lean_ctor_set(v___x_639_, 1, v___x_645_);
lean_ctor_set(v___x_639_, 0, v___x_643_);
v___x_669_ = v___x_639_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_645_);
v___x_669_ = v_reuseFailAlloc_673_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_671_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_669_);
v___x_671_ = v___x_666_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec(v___x_643_);
lean_del_object(v___x_639_);
v_a_676_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_664_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_664_);
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
lean_dec(v___x_643_);
v_declName_686_ = lean_ctor_get(v_a_651_, 0);
lean_inc(v_declName_686_);
lean_dec_ref_known(v_a_651_, 1);
v___x_687_ = l_Lean_Compiler_LCNF_eraseDecl(v___x_622_, v___x_649_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_697_; 
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v___x_687_, 0);
lean_dec(v_unused_698_);
v___x_689_ = v___x_687_;
v_isShared_690_ = v_isSharedCheck_697_;
goto v_resetjp_688_;
}
else
{
lean_dec(v___x_687_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_697_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set_tag(v___x_639_, 9);
lean_ctor_set(v___x_639_, 1, v___x_645_);
lean_ctor_set(v___x_639_, 0, v_declName_686_);
v___x_692_ = v___x_639_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_declName_686_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v___x_645_);
v___x_692_ = v_reuseFailAlloc_696_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_692_);
v___x_694_ = v___x_689_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_declName_686_);
lean_del_object(v___x_639_);
v_a_699_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_687_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_687_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref_known(v___x_649_, 3);
lean_dec(v___x_643_);
lean_del_object(v___x_639_);
v_a_707_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_650_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_650_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec(v_a_625_);
lean_del_object(v___x_620_);
lean_dec_ref(v_expectedType_599_);
v_a_718_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_628_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_628_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_del_object(v___x_620_);
lean_dec_ref(v_expectedType_599_);
lean_dec_ref(v_fvarIdType_598_);
v_a_726_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_624_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_624_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec_ref(v_expectedType_599_);
lean_dec_ref(v_fvarIdType_598_);
lean_dec(v_fvarId_597_);
v_a_736_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_609_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_609_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec_ref(v_expectedType_599_);
lean_dec_ref(v_fvarIdType_598_);
v___x_744_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_744_, 0, v_fvarId_597_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___boxed(lean_object* v_fvarId_746_, lean_object* v_fvarIdType_747_, lean_object* v_expectedType_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_746_, v_fvarIdType_747_, v_expectedType_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(lean_object* v_fvarId_757_, lean_object* v_expectedType_758_, lean_object* v_k_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_767_; 
lean_inc(v_fvarId_757_);
v___x_767_ = l_Lean_Compiler_LCNF_getType(v_fvarId_757_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; uint8_t v___x_769_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
v___x_769_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_768_, v_expectedType_758_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_inc_ref(v_expectedType_758_);
v___x_770_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_757_, v_a_768_, v_expectedType_758_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
v___x_772_ = 1;
v___x_773_ = lean_box(0);
v___x_774_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_772_, v___x_773_, v_expectedType_758_, v_a_771_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v_fvarId_776_; lean_object* v___x_777_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
v_fvarId_776_ = lean_ctor_get(v_a_775_, 0);
lean_inc(v_a_765_);
lean_inc_ref(v_a_764_);
lean_inc(v_a_763_);
lean_inc_ref(v_a_762_);
lean_inc(v_a_761_);
lean_inc_ref(v_a_760_);
lean_inc(v_fvarId_776_);
v___x_777_ = lean_apply_8(v_k_759_, v_fvarId_776_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, lean_box(0));
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_786_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_786_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_a_775_);
lean_ctor_set(v___x_782_, 1, v_a_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_dec(v_a_775_);
return v___x_777_;
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v_k_759_);
v_a_787_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_774_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_774_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v_k_759_);
lean_dec_ref(v_expectedType_758_);
v_a_795_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_770_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_770_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v___x_803_; 
lean_dec(v_a_768_);
lean_dec_ref(v_expectedType_758_);
lean_inc(v_a_765_);
lean_inc_ref(v_a_764_);
lean_inc(v_a_763_);
lean_inc_ref(v_a_762_);
lean_inc(v_a_761_);
lean_inc_ref(v_a_760_);
v___x_803_ = lean_apply_8(v_k_759_, v_fvarId_757_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, lean_box(0));
return v___x_803_;
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v_k_759_);
lean_dec_ref(v_expectedType_758_);
lean_dec(v_fvarId_757_);
v_a_804_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_767_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_767_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded___boxed(lean_object* v_fvarId_812_, lean_object* v_expectedType_813_, lean_object* v_k_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(v_fvarId_812_, v_expectedType_813_, v_k_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(lean_object* v_arg_823_, lean_object* v_k_824_, lean_object* v_x_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(v_arg_823_, v_x_825_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
lean_inc(v___y_829_);
lean_inc_ref(v___y_828_);
lean_inc(v___y_827_);
lean_inc_ref(v___y_826_);
v___x_834_ = lean_apply_8(v_k_824_, v___x_833_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, lean_box(0));
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0___boxed(lean_object* v_arg_835_, lean_object* v_k_836_, lean_object* v_x_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_835_, v_k_836_, v_x_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(lean_object* v_arg_846_, lean_object* v_expectedType_847_, lean_object* v_k_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
if (lean_obj_tag(v_arg_846_) == 0)
{
lean_object* v___x_856_; 
lean_dec_ref(v_expectedType_847_);
lean_inc(v_a_854_);
lean_inc_ref(v_a_853_);
lean_inc(v_a_852_);
lean_inc_ref(v_a_851_);
lean_inc(v_a_850_);
lean_inc_ref(v_a_849_);
v___x_856_ = lean_apply_8(v_k_848_, v_arg_846_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, lean_box(0));
return v___x_856_;
}
else
{
lean_object* v_fvarId_857_; lean_object* v___x_858_; 
v_fvarId_857_ = lean_ctor_get(v_arg_846_, 0);
lean_inc(v_fvarId_857_);
v___x_858_ = l_Lean_Compiler_LCNF_getType(v_fvarId_857_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; uint8_t v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_859_, v_expectedType_847_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
lean_inc_ref(v_expectedType_847_);
lean_inc(v_fvarId_857_);
v___x_861_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_857_, v_a_859_, v_expectedType_847_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; uint8_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_861_, 1);
v___x_863_ = 1;
v___x_864_ = lean_box(0);
v___x_865_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_863_, v___x_864_, v_expectedType_847_, v_a_862_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v_fvarId_867_; lean_object* v___x_868_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_865_, 1);
v_fvarId_867_ = lean_ctor_get(v_a_866_, 0);
lean_inc(v_fvarId_867_);
v___x_868_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_846_, v_k_848_, v_fvarId_867_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_877_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_877_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_a_866_);
lean_ctor_set(v___x_873_, 1, v_a_869_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_873_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
else
{
lean_dec(v_a_866_);
return v___x_868_;
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref_known(v_arg_846_, 1);
lean_dec_ref(v_k_848_);
v_a_878_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_865_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_865_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref_known(v_arg_846_, 1);
lean_dec_ref(v_k_848_);
lean_dec_ref(v_expectedType_847_);
v_a_886_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_861_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_861_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v___x_894_; 
lean_inc(v_fvarId_857_);
lean_dec(v_a_859_);
lean_dec_ref(v_expectedType_847_);
v___x_894_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(v_arg_846_, v_k_848_, v_fvarId_857_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
return v___x_894_;
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref_known(v_arg_846_, 1);
lean_dec_ref(v_k_848_);
lean_dec_ref(v_expectedType_847_);
v_a_895_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_858_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_858_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___boxed(lean_object* v_arg_903_, lean_object* v_expectedType_904_, lean_object* v_k_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(v_arg_903_, v_expectedType_904_, v_k_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(lean_object* v_upperBound_914_, lean_object* v_args_915_, lean_object* v_typeFromIdx_916_, lean_object* v_a_917_, lean_object* v_b_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_a_927_; uint8_t v___x_931_; 
v___x_931_ = lean_nat_dec_lt(v_a_917_, v_upperBound_914_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec(v_a_917_);
lean_dec_ref(v_typeFromIdx_916_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v_b_918_);
return v___x_932_;
}
else
{
lean_object* v_fst_933_; lean_object* v_snd_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_997_; 
v_fst_933_ = lean_ctor_get(v_b_918_, 0);
v_snd_934_ = lean_ctor_get(v_b_918_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_b_918_);
if (v_isSharedCheck_997_ == 0)
{
v___x_936_ = v_b_918_;
v_isShared_937_ = v_isSharedCheck_997_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_snd_934_);
lean_inc(v_fst_933_);
lean_dec(v_b_918_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_997_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; 
v___x_938_ = lean_array_fget(v_args_915_, v_a_917_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_939_ = lean_array_push(v_fst_933_, v___x_938_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_939_);
v___x_941_ = v___x_936_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_snd_934_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
v_a_927_ = v___x_941_;
goto v___jp_926_;
}
}
else
{
lean_object* v_fvarId_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_fvarId_943_ = lean_ctor_get(v___x_938_, 0);
lean_inc_ref(v_typeFromIdx_916_);
lean_inc(v_a_917_);
v___x_944_ = lean_apply_1(v_typeFromIdx_916_, v_a_917_);
lean_inc(v_fvarId_943_);
v___x_945_ = l_Lean_Compiler_LCNF_getType(v_fvarId_943_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; uint8_t v___x_947_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref_known(v___x_945_, 1);
v___x_947_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_946_, v___x_944_);
if (v___x_947_ == 0)
{
lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_983_; 
lean_inc(v_fvarId_943_);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v___x_938_, 0);
lean_dec(v_unused_984_);
v___x_949_ = v___x_938_;
v_isShared_950_ = v_isSharedCheck_983_;
goto v_resetjp_948_;
}
else
{
lean_dec(v___x_938_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_983_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; 
lean_inc_ref(v___x_944_);
v___x_951_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_943_, v_a_946_, v___x_944_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = 1;
v___x_954_ = lean_box(0);
v___x_955_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_953_, v___x_954_, v___x_944_, v_a_952_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v_fvarId_957_; lean_object* v___x_959_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 1);
v_fvarId_957_ = lean_ctor_get(v_a_956_, 0);
lean_inc(v_fvarId_957_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v_fvarId_957_);
v___x_959_ = v___x_949_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_fvarId_957_);
v___x_959_ = v_reuseFailAlloc_966_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_960_ = lean_array_push(v_fst_933_, v___x_959_);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v_a_956_);
v___x_962_ = lean_array_push(v_snd_934_, v___x_961_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v___x_962_);
lean_ctor_set(v___x_936_, 0, v___x_960_);
v___x_964_ = v___x_936_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
v_a_927_ = v___x_964_;
goto v___jp_926_;
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_del_object(v___x_949_);
lean_del_object(v___x_936_);
lean_dec(v_snd_934_);
lean_dec(v_fst_933_);
lean_dec(v_a_917_);
lean_dec_ref(v_typeFromIdx_916_);
v_a_967_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_955_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_955_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_del_object(v___x_949_);
lean_dec_ref(v___x_944_);
lean_del_object(v___x_936_);
lean_dec(v_snd_934_);
lean_dec(v_fst_933_);
lean_dec(v_a_917_);
lean_dec_ref(v_typeFromIdx_916_);
v_a_975_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_951_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_951_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
else
{
lean_object* v___x_985_; lean_object* v___x_987_; 
lean_dec(v_a_946_);
lean_dec_ref(v___x_944_);
v___x_985_ = lean_array_push(v_fst_933_, v___x_938_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_985_);
v___x_987_ = v___x_936_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_snd_934_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
v_a_927_ = v___x_987_;
goto v___jp_926_;
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec_ref(v___x_944_);
lean_dec_ref_known(v___x_938_, 1);
lean_del_object(v___x_936_);
lean_dec(v_snd_934_);
lean_dec(v_fst_933_);
lean_dec(v_a_917_);
lean_dec_ref(v_typeFromIdx_916_);
v_a_989_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_945_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_945_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
}
v___jp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_unsigned_to_nat(1u);
v___x_929_ = lean_nat_add(v_a_917_, v___x_928_);
lean_dec(v_a_917_);
v_a_917_ = v___x_929_;
v_b_918_ = v_a_927_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg___boxed(lean_object* v_upperBound_998_, lean_object* v_args_999_, lean_object* v_typeFromIdx_1000_, lean_object* v_a_1001_, lean_object* v_b_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v_upperBound_998_, v_args_999_, v_typeFromIdx_1000_, v_a_1001_, v_b_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec_ref(v_args_999_);
lean_dec(v_upperBound_998_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(lean_object* v_args_1011_, lean_object* v_typeFromIdx_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1020_; lean_object* v_newArgs_1021_; lean_object* v___x_1022_; lean_object* v_casters_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1020_ = lean_array_get_size(v_args_1011_);
v_newArgs_1021_ = lean_mk_empty_array_with_capacity(v___x_1020_);
v___x_1022_ = lean_unsigned_to_nat(0u);
v_casters_1023_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0));
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v_newArgs_1021_);
lean_ctor_set(v___x_1024_, 1, v_casters_1023_);
v___x_1025_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v___x_1020_, v_args_1011_, v_typeFromIdx_1012_, v___x_1022_, v___x_1024_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1042_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1042_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1042_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_fst_1030_; lean_object* v_snd_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1041_; 
v_fst_1030_ = lean_ctor_get(v_a_1026_, 0);
v_snd_1031_ = lean_ctor_get(v_a_1026_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_a_1026_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1033_ = v_a_1026_;
v_isShared_1034_ = v_isSharedCheck_1041_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_snd_1031_);
lean_inc(v_fst_1030_);
lean_dec(v_a_1026_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1041_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_fst_1030_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_snd_1031_);
v___x_1036_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1036_);
v___x_1038_ = v___x_1028_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
else
{
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux___boxed(lean_object* v_args_1043_, lean_object* v_typeFromIdx_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1043_, v_typeFromIdx_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec_ref(v_args_1043_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(lean_object* v_upperBound_1053_, lean_object* v_args_1054_, lean_object* v_typeFromIdx_1055_, lean_object* v_inst_1056_, lean_object* v_R_1057_, lean_object* v_a_1058_, lean_object* v_b_1059_, lean_object* v_c_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(v_upperBound_1053_, v_args_1054_, v_typeFromIdx_1055_, v_a_1058_, v_b_1059_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___boxed(lean_object* v_upperBound_1069_, lean_object* v_args_1070_, lean_object* v_typeFromIdx_1071_, lean_object* v_inst_1072_, lean_object* v_R_1073_, lean_object* v_a_1074_, lean_object* v_b_1075_, lean_object* v_c_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(v_upperBound_1069_, v_args_1070_, v_typeFromIdx_1071_, v_inst_1072_, v_R_1073_, v_a_1074_, v_b_1075_, v_c_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec_ref(v_args_1070_);
lean_dec(v_upperBound_1069_);
return v_res_1084_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
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
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1118_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1118_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1118_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_1108_, v_a_1110_);
lean_dec(v_snd_1108_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1114_);
v___x_1116_ = v___x_1112_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
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
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec_ref(v_k_1096_);
v_a_1119_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1105_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1105_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___boxed(lean_object* v_args_1127_, lean_object* v_ps_1128_, lean_object* v_k_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(v_args_1127_, v_ps_1128_, v_k_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec_ref(v_args_1127_);
return v_res_1137_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_box(0);
v___x_1142_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1));
v___x_1143_ = l_Lean_Expr_const___override(v___x_1142_, v___x_1141_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(lean_object* v_x_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___boxed(lean_object* v_x_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(v_x_1146_);
lean_dec(v_x_1146_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(lean_object* v_args_1149_, lean_object* v_k_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v___f_1158_; lean_object* v___x_1159_; 
v___f_1158_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0));
v___x_1159_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_1149_, v___f_1158_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v_fst_1161_; lean_object* v_snd_1162_; lean_object* v___x_1163_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1159_, 1);
v_fst_1161_ = lean_ctor_get(v_a_1160_, 0);
lean_inc(v_fst_1161_);
v_snd_1162_ = lean_ctor_get(v_a_1160_, 1);
lean_inc(v_snd_1162_);
lean_dec(v_a_1160_);
lean_inc(v_a_1156_);
lean_inc_ref(v_a_1155_);
lean_inc(v_a_1154_);
lean_inc_ref(v_a_1153_);
lean_inc(v_a_1152_);
lean_inc_ref(v_a_1151_);
v___x_1163_ = lean_apply_8(v_k_1150_, v_fst_1161_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, lean_box(0));
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1172_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1168_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_1162_, v_a_1164_);
lean_dec(v_snd_1162_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1168_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_dec(v_snd_1162_);
return v___x_1163_;
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v_k_1150_);
v_a_1173_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1159_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1159_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___boxed(lean_object* v_args_1181_, lean_object* v_k_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(v_args_1181_, v_k_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec_ref(v_args_1181_);
return v_res_1190_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(lean_object* v_msg_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
v___x_1194_ = lean_panic_fn_borrowed(v___x_1193_, v_msg_1192_);
return v___x_1194_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1198_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1199_ = lean_unsigned_to_nat(9u);
v___x_1200_ = lean_unsigned_to_nat(625u);
v___x_1201_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1));
v___x_1202_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0));
v___x_1203_ = l_mkPanicMessageWithDecl(v___x_1202_, v___x_1201_, v___x_1200_, v___x_1199_, v___x_1198_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(lean_object* v_code_1204_, lean_object* v_decl_1205_, lean_object* v_k_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v_type_1212_; lean_object* v_value_1213_; uint8_t v___x_1214_; 
v_type_1212_ = lean_ctor_get(v_decl_1205_, 2);
v_value_1213_ = lean_ctor_get(v_decl_1205_, 3);
v___x_1214_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_1212_);
if (v___x_1214_ == 0)
{
if (lean_obj_tag(v_code_1204_) == 0)
{
lean_object* v_decl_1215_; lean_object* v_k_1216_; size_t v___x_1217_; size_t v___x_1218_; uint8_t v___x_1219_; 
v_decl_1215_ = lean_ctor_get(v_code_1204_, 0);
v_k_1216_ = lean_ctor_get(v_code_1204_, 1);
v___x_1217_ = lean_ptr_addr(v_k_1216_);
v___x_1218_ = lean_ptr_addr(v_k_1206_);
v___x_1219_ = lean_usize_dec_eq(v___x_1217_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1227_; 
v_isSharedCheck_1227_ = !lean_is_exclusive(v_code_1204_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; lean_object* v_unused_1229_; 
v_unused_1228_ = lean_ctor_get(v_code_1204_, 1);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_code_1204_, 0);
lean_dec(v_unused_1229_);
v___x_1221_ = v_code_1204_;
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
else
{
lean_dec(v_code_1204_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v_k_1206_);
lean_ctor_set(v___x_1221_, 0, v_decl_1205_);
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_decl_1205_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_k_1206_);
v___x_1224_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
}
}
else
{
size_t v___x_1230_; size_t v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = lean_ptr_addr(v_decl_1215_);
v___x_1231_ = lean_ptr_addr(v_decl_1205_);
v___x_1232_ = lean_usize_dec_eq(v___x_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1240_; 
v_isSharedCheck_1240_ = !lean_is_exclusive(v_code_1204_);
if (v_isSharedCheck_1240_ == 0)
{
lean_object* v_unused_1241_; lean_object* v_unused_1242_; 
v_unused_1241_ = lean_ctor_get(v_code_1204_, 1);
lean_dec(v_unused_1241_);
v_unused_1242_ = lean_ctor_get(v_code_1204_, 0);
lean_dec(v_unused_1242_);
v___x_1234_ = v_code_1204_;
v_isShared_1235_ = v_isSharedCheck_1240_;
goto v_resetjp_1233_;
}
else
{
lean_dec(v_code_1204_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1240_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 1, v_k_1206_);
lean_ctor_set(v___x_1234_, 0, v_decl_1205_);
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_decl_1205_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_k_1206_);
v___x_1237_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
}
}
else
{
lean_object* v___x_1243_; 
lean_dec_ref(v_k_1206_);
lean_dec_ref(v_decl_1205_);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_code_1204_);
return v___x_1243_;
}
}
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec_ref(v_k_1206_);
lean_dec_ref(v_decl_1205_);
lean_dec_ref(v_code_1204_);
v___x_1244_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_1245_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_1244_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
else
{
uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec_ref(v_code_1204_);
v___x_1247_ = 1;
v___x_1248_ = lean_box(0);
v___x_1249_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
lean_inc(v_value_1213_);
v___x_1250_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1247_, v___x_1248_, v___x_1249_, v_value_1213_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v_fvarId_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v_fvarId_1252_ = lean_ctor_get(v_a_1251_, 0);
lean_inc(v_fvarId_1252_);
v___x_1253_ = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(v___x_1253_, 0, v_fvarId_1252_);
v___x_1254_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1247_, v_decl_1205_, v___x_1253_, v_a_1208_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1264_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v_a_1255_);
lean_ctor_set(v___x_1259_, 1, v_k_1206_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v_a_1251_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1260_);
v___x_1262_ = v___x_1257_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_a_1251_);
lean_dec_ref(v_k_1206_);
v_a_1265_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1254_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1254_);
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
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v_k_1206_);
lean_dec_ref(v_decl_1205_);
v_a_1273_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1250_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1250_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___boxed(lean_object* v_code_1281_, lean_object* v_decl_1282_, lean_object* v_k_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1281_, v_decl_1282_, v_k_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(lean_object* v_code_1290_, lean_object* v_decl_1291_, lean_object* v_k_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1290_, v_decl_1291_, v_k_1292_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___boxed(lean_object* v_code_1301_, lean_object* v_decl_1302_, lean_object* v_k_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(v_code_1301_, v_decl_1302_, v_k_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(lean_object* v_code_1312_, lean_object* v_decl_1313_, lean_object* v_expType_1314_, lean_object* v_k_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v_type_1323_; lean_object* v_value_1324_; uint8_t v___x_1325_; 
v_type_1323_ = lean_ctor_get(v_decl_1313_, 2);
v_value_1324_ = lean_ctor_get(v_decl_1313_, 3);
v___x_1325_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_type_1323_, v_expType_1314_);
if (v___x_1325_ == 0)
{
lean_object* v_boxedTy_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec_ref(v_code_1312_);
v_boxedTy_1326_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_type_1323_);
v___x_1327_ = 1;
v___x_1328_ = lean_box(0);
lean_inc(v_value_1324_);
v___x_1329_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1327_, v___x_1328_, v_boxedTy_1326_, v_value_1324_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v_fvarId_1331_; lean_object* v_type_1332_; lean_object* v___x_1333_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v_fvarId_1331_ = lean_ctor_get(v_a_1330_, 0);
v_type_1332_ = lean_ctor_get(v_a_1330_, 2);
lean_inc_ref(v_type_1323_);
lean_inc_ref(v_type_1332_);
lean_inc(v_fvarId_1331_);
v___x_1333_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_1331_, v_type_1332_, v_type_1323_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1335_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v___x_1335_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1327_, v_decl_1313_, v_a_1334_, v_a_1319_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1345_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1345_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1345_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1340_, 0, v_a_1336_);
lean_ctor_set(v___x_1340_, 1, v_k_1315_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_a_1330_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1341_);
v___x_1343_ = v___x_1338_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_a_1330_);
lean_dec_ref(v_k_1315_);
v_a_1346_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1335_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1335_);
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
lean_dec(v_a_1330_);
lean_dec_ref(v_k_1315_);
lean_dec_ref(v_decl_1313_);
v_a_1354_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1333_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1333_);
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
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v_k_1315_);
lean_dec_ref(v_decl_1313_);
v_a_1362_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1329_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1329_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
if (lean_obj_tag(v_code_1312_) == 0)
{
lean_object* v_decl_1370_; lean_object* v_k_1371_; size_t v___x_1372_; size_t v___x_1373_; uint8_t v___x_1374_; 
v_decl_1370_ = lean_ctor_get(v_code_1312_, 0);
v_k_1371_ = lean_ctor_get(v_code_1312_, 1);
v___x_1372_ = lean_ptr_addr(v_k_1371_);
v___x_1373_ = lean_ptr_addr(v_k_1315_);
v___x_1374_ = lean_usize_dec_eq(v___x_1372_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1382_; 
v_isSharedCheck_1382_ = !lean_is_exclusive(v_code_1312_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; lean_object* v_unused_1384_; 
v_unused_1383_ = lean_ctor_get(v_code_1312_, 1);
lean_dec(v_unused_1383_);
v_unused_1384_ = lean_ctor_get(v_code_1312_, 0);
lean_dec(v_unused_1384_);
v___x_1376_ = v_code_1312_;
v_isShared_1377_ = v_isSharedCheck_1382_;
goto v_resetjp_1375_;
}
else
{
lean_dec(v_code_1312_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1382_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 1, v_k_1315_);
lean_ctor_set(v___x_1376_, 0, v_decl_1313_);
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_decl_1313_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_k_1315_);
v___x_1379_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
}
else
{
size_t v___x_1385_; size_t v___x_1386_; uint8_t v___x_1387_; 
v___x_1385_ = lean_ptr_addr(v_decl_1370_);
v___x_1386_ = lean_ptr_addr(v_decl_1313_);
v___x_1387_ = lean_usize_dec_eq(v___x_1385_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1395_; 
v_isSharedCheck_1395_ = !lean_is_exclusive(v_code_1312_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; lean_object* v_unused_1397_; 
v_unused_1396_ = lean_ctor_get(v_code_1312_, 1);
lean_dec(v_unused_1396_);
v_unused_1397_ = lean_ctor_get(v_code_1312_, 0);
lean_dec(v_unused_1397_);
v___x_1389_ = v_code_1312_;
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
else
{
lean_dec(v_code_1312_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 1, v_k_1315_);
lean_ctor_set(v___x_1389_, 0, v_decl_1313_);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_decl_1313_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_k_1315_);
v___x_1392_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
}
}
else
{
lean_object* v___x_1398_; 
lean_dec_ref(v_k_1315_);
lean_dec_ref(v_decl_1313_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v_code_1312_);
return v___x_1398_;
}
}
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec_ref(v_k_1315_);
lean_dec_ref(v_decl_1313_);
lean_dec_ref(v_code_1312_);
v___x_1399_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_1400_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_1399_);
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
return v___x_1401_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded___boxed(lean_object* v_code_1402_, lean_object* v_decl_1403_, lean_object* v_expType_1404_, lean_object* v_k_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(v_code_1402_, v_decl_1403_, v_expType_1404_, v_k_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec_ref(v_expType_1404_);
return v_res_1413_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_instMonadEIO___redArg();
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(lean_object* v_msg_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v_toApplicative_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1492_; 
v___x_1427_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
v___x_1428_ = l_StateRefT_x27_instMonad___redArg(v___x_1427_);
v_toApplicative_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; 
v_unused_1493_ = lean_ctor_get(v___x_1428_, 1);
lean_dec(v_unused_1493_);
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1492_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_toApplicative_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1492_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_toFunctor_1433_; lean_object* v_toSeq_1434_; lean_object* v_toSeqLeft_1435_; lean_object* v_toSeqRight_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1490_; 
v_toFunctor_1433_ = lean_ctor_get(v_toApplicative_1429_, 0);
v_toSeq_1434_ = lean_ctor_get(v_toApplicative_1429_, 2);
v_toSeqLeft_1435_ = lean_ctor_get(v_toApplicative_1429_, 3);
v_toSeqRight_1436_ = lean_ctor_get(v_toApplicative_1429_, 4);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_toApplicative_1429_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; 
v_unused_1491_ = lean_ctor_get(v_toApplicative_1429_, 1);
lean_dec(v_unused_1491_);
v___x_1438_ = v_toApplicative_1429_;
v_isShared_1439_ = v_isSharedCheck_1490_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_toSeqRight_1436_);
lean_inc(v_toSeqLeft_1435_);
lean_inc(v_toSeq_1434_);
lean_inc(v_toFunctor_1433_);
lean_dec(v_toApplicative_1429_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1490_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___f_1440_; lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___x_1444_; lean_object* v___f_1445_; lean_object* v___f_1446_; lean_object* v___f_1447_; lean_object* v___x_1449_; 
v___f_1440_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1));
v___f_1441_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1433_);
v___f_1442_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1442_, 0, v_toFunctor_1433_);
v___f_1443_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1443_, 0, v_toFunctor_1433_);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___f_1442_);
lean_ctor_set(v___x_1444_, 1, v___f_1443_);
v___f_1445_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1445_, 0, v_toSeqRight_1436_);
v___f_1446_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1446_, 0, v_toSeqLeft_1435_);
v___f_1447_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1447_, 0, v_toSeq_1434_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 4, v___f_1445_);
lean_ctor_set(v___x_1438_, 3, v___f_1446_);
lean_ctor_set(v___x_1438_, 2, v___f_1447_);
lean_ctor_set(v___x_1438_, 1, v___f_1440_);
lean_ctor_set(v___x_1438_, 0, v___x_1444_);
v___x_1449_ = v___x_1438_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v___f_1440_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v___f_1447_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v___f_1446_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v___f_1445_);
v___x_1449_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1451_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___f_1441_);
lean_ctor_set(v___x_1431_, 0, v___x_1449_);
v___x_1451_ = v___x_1431_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___f_1441_);
v___x_1451_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; lean_object* v_toApplicative_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1486_; 
v___x_1452_ = l_StateRefT_x27_instMonad___redArg(v___x_1451_);
v_toApplicative_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v___x_1452_, 1);
lean_dec(v_unused_1487_);
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1486_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_toApplicative_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1486_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v_toFunctor_1457_; lean_object* v_toSeq_1458_; lean_object* v_toSeqLeft_1459_; lean_object* v_toSeqRight_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1484_; 
v_toFunctor_1457_ = lean_ctor_get(v_toApplicative_1453_, 0);
v_toSeq_1458_ = lean_ctor_get(v_toApplicative_1453_, 2);
v_toSeqLeft_1459_ = lean_ctor_get(v_toApplicative_1453_, 3);
v_toSeqRight_1460_ = lean_ctor_get(v_toApplicative_1453_, 4);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_toApplicative_1453_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; 
v_unused_1485_ = lean_ctor_get(v_toApplicative_1453_, 1);
lean_dec(v_unused_1485_);
v___x_1462_ = v_toApplicative_1453_;
v_isShared_1463_ = v_isSharedCheck_1484_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_toSeqRight_1460_);
lean_inc(v_toSeqLeft_1459_);
lean_inc(v_toSeq_1458_);
lean_inc(v_toFunctor_1457_);
lean_dec(v_toApplicative_1453_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1484_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___f_1464_; lean_object* v___f_1465_; lean_object* v___f_1466_; lean_object* v___f_1467_; lean_object* v___x_1468_; lean_object* v___f_1469_; lean_object* v___f_1470_; lean_object* v___f_1471_; lean_object* v___x_1473_; 
v___f_1464_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3));
v___f_1465_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1457_);
v___f_1466_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1466_, 0, v_toFunctor_1457_);
v___f_1467_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1467_, 0, v_toFunctor_1457_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___f_1466_);
lean_ctor_set(v___x_1468_, 1, v___f_1467_);
v___f_1469_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1469_, 0, v_toSeqRight_1460_);
v___f_1470_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1470_, 0, v_toSeqLeft_1459_);
v___f_1471_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1471_, 0, v_toSeq_1458_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 4, v___f_1469_);
lean_ctor_set(v___x_1462_, 3, v___f_1470_);
lean_ctor_set(v___x_1462_, 2, v___f_1471_);
lean_ctor_set(v___x_1462_, 1, v___f_1464_);
lean_ctor_set(v___x_1462_, 0, v___x_1468_);
v___x_1473_ = v___x_1462_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v___f_1464_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v___f_1471_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v___f_1470_);
lean_ctor_set(v_reuseFailAlloc_1483_, 4, v___f_1469_);
v___x_1473_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1475_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v___f_1465_);
lean_ctor_set(v___x_1455_, 0, v___x_1473_);
v___x_1475_ = v___x_1455_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___f_1465_);
v___x_1475_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___f_1479_; lean_object* v___x_3202__overap_1480_; lean_object* v___x_1481_; 
v___x_1476_ = l_StateRefT_x27_instMonad___redArg(v___x_1475_);
v___x_1477_ = l_Lean_instInhabitedExpr;
v___x_1478_ = l_instInhabitedOfMonad___redArg(v___x_1476_, v___x_1477_);
v___f_1479_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1479_, 0, v___x_1478_);
v___x_3202__overap_1480_ = lean_panic_fn_borrowed(v___f_1479_, v_msg_1419_);
lean_dec_ref(v___f_1479_);
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1424_);
lean_inc(v___y_1423_);
lean_inc_ref(v___y_1422_);
lean_inc(v___y_1421_);
lean_inc_ref(v___y_1420_);
v___x_1481_ = lean_apply_7(v___x_3202__overap_1480_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, lean_box(0));
return v___x_1481_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___boxed(lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v_msg_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
return v_res_1502_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1506_ = lean_unsigned_to_nat(44u);
v___x_1507_ = lean_unsigned_to_nat(316u);
v___x_1508_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1));
v___x_1509_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1510_ = l_mkPanicMessageWithDecl(v___x_1509_, v___x_1508_, v___x_1507_, v___x_1506_, v___x_1505_);
return v___x_1510_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = lean_box(0);
v___x_1515_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4));
v___x_1516_ = l_Lean_Expr_const___override(v___x_1515_, v___x_1514_);
return v___x_1516_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = lean_box(0);
v___x_1521_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7));
v___x_1522_ = l_Lean_Expr_const___override(v___x_1521_, v___x_1520_);
return v___x_1522_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1526_ = lean_box(0);
v___x_1527_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10));
v___x_1528_ = l_Lean_Expr_const___override(v___x_1527_, v___x_1526_);
return v___x_1528_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1529_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1530_ = lean_unsigned_to_nat(45u);
v___x_1531_ = lean_unsigned_to_nat(301u);
v___x_1532_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1));
v___x_1533_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1534_ = l_mkPanicMessageWithDecl(v___x_1533_, v___x_1532_, v___x_1531_, v___x_1530_, v___x_1529_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(lean_object* v_currentType_1535_, lean_object* v_value_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; 
switch(lean_obj_tag(v_value_1536_))
{
case 0:
{
lean_object* v_value_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1583_; 
v_value_1553_ = lean_ctor_get(v_value_1536_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_value_1536_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1555_ = v_value_1536_;
v_isShared_1556_ = v_isSharedCheck_1583_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_value_1553_);
lean_dec(v_value_1536_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1583_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
switch(lean_obj_tag(v_value_1553_))
{
case 0:
{
lean_object* v_val_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1570_; 
lean_del_object(v___x_1555_);
v_val_1557_ = lean_ctor_get(v_value_1553_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_value_1553_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1559_ = v_value_1553_;
v_isShared_1560_ = v_isSharedCheck_1570_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_val_1557_);
lean_dec(v_value_1553_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1570_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1561_ = l_Lean_maxSmallNat;
v___x_1562_ = lean_nat_dec_le(v_val_1557_, v___x_1561_);
lean_dec(v_val_1557_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1564_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v_currentType_1535_);
v___x_1564_ = v___x_1559_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_currentType_1535_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
lean_dec_ref(v_currentType_1535_);
v___x_1566_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1566_);
v___x_1568_ = v___x_1559_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
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
case 1:
{
lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1578_; 
lean_del_object(v___x_1555_);
lean_dec_ref(v_currentType_1535_);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_value_1553_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v_value_1553_, 0);
lean_dec(v_unused_1579_);
v___x_1572_ = v_value_1553_;
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
else
{
lean_dec(v_value_1553_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1574_);
v___x_1576_ = v___x_1572_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
default: 
{
lean_object* v___x_1581_; 
lean_dec_ref(v_value_1553_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v_currentType_1535_);
v___x_1581_ = v___x_1555_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_currentType_1535_);
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
}
case 1:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec_ref(v_currentType_1535_);
v___x_1584_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
case 5:
{
lean_object* v_i_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec_ref(v_currentType_1535_);
v_i_1586_ = lean_ctor_get(v_value_1536_, 0);
lean_inc_ref(v_i_1586_);
lean_dec_ref_known(v_value_1536_, 2);
v___x_1587_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_i_1586_);
lean_dec_ref(v_i_1586_);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
case 7:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec_ref_known(v_value_1536_, 2);
lean_dec_ref(v_currentType_1535_);
v___x_1589_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
case 9:
{
lean_object* v_fn_1591_; lean_object* v___x_1592_; 
lean_dec_ref(v_currentType_1535_);
v_fn_1591_ = lean_ctor_get(v_value_1536_, 0);
lean_inc(v_fn_1591_);
lean_dec_ref_known(v_value_1536_, 2);
v___x_1592_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_1591_, v_a_1542_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1604_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1604_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1604_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
if (lean_obj_tag(v_a_1593_) == 1)
{
lean_object* v_val_1597_; lean_object* v_type_1598_; lean_object* v___x_1600_; 
v_val_1597_ = lean_ctor_get(v_a_1593_, 0);
lean_inc(v_val_1597_);
lean_dec_ref_known(v_a_1593_, 1);
v_type_1598_ = lean_ctor_get(v_val_1597_, 2);
lean_inc_ref(v_type_1598_);
lean_dec(v_val_1597_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v_type_1598_);
v___x_1600_ = v___x_1595_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_type_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_del_object(v___x_1595_);
lean_dec(v_a_1593_);
v___x_1602_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12);
v___x_1603_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1602_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
return v___x_1603_;
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_a_1605_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1592_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1592_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
case 10:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec_ref_known(v_value_1536_, 2);
lean_dec_ref(v_currentType_1535_);
v___x_1613_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
return v___x_1614_;
}
case 13:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec_ref_known(v_value_1536_, 2);
lean_dec_ref(v_currentType_1535_);
v___x_1615_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
v___x_1616_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1615_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
return v___x_1616_;
}
case 14:
{
lean_dec_ref_known(v_value_1536_, 1);
lean_dec_ref(v_currentType_1535_);
v___y_1545_ = v_a_1537_;
v___y_1546_ = v_a_1538_;
v___y_1547_ = v_a_1539_;
v___y_1548_ = v_a_1540_;
v___y_1549_ = v_a_1541_;
v___y_1550_ = v_a_1542_;
goto v___jp_1544_;
}
case 15:
{
lean_dec_ref_known(v_value_1536_, 1);
lean_dec_ref(v_currentType_1535_);
v___y_1545_ = v_a_1537_;
v___y_1546_ = v_a_1538_;
v___y_1547_ = v_a_1539_;
v___y_1548_ = v_a_1540_;
v___y_1549_ = v_a_1541_;
v___y_1550_ = v_a_1542_;
goto v___jp_1544_;
}
default: 
{
lean_object* v___x_1617_; 
lean_dec(v_value_1536_);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v_currentType_1535_);
return v___x_1617_;
}
}
v___jp_1544_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
v___x_1552_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(v___x_1551_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___boxed(lean_object* v_currentType_1618_, lean_object* v_value_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(v_currentType_1618_, v_value_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(lean_object* v_msg_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v_toApplicative_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1701_; 
v___x_1636_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
v___x_1637_ = l_StateRefT_x27_instMonad___redArg(v___x_1636_);
v_toApplicative_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; 
v_unused_1702_ = lean_ctor_get(v___x_1637_, 1);
lean_dec(v_unused_1702_);
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1701_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_toApplicative_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1701_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v_toFunctor_1642_; lean_object* v_toSeq_1643_; lean_object* v_toSeqLeft_1644_; lean_object* v_toSeqRight_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1699_; 
v_toFunctor_1642_ = lean_ctor_get(v_toApplicative_1638_, 0);
v_toSeq_1643_ = lean_ctor_get(v_toApplicative_1638_, 2);
v_toSeqLeft_1644_ = lean_ctor_get(v_toApplicative_1638_, 3);
v_toSeqRight_1645_ = lean_ctor_get(v_toApplicative_1638_, 4);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_toApplicative_1638_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; 
v_unused_1700_ = lean_ctor_get(v_toApplicative_1638_, 1);
lean_dec(v_unused_1700_);
v___x_1647_ = v_toApplicative_1638_;
v_isShared_1648_ = v_isSharedCheck_1699_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_toSeqRight_1645_);
lean_inc(v_toSeqLeft_1644_);
lean_inc(v_toSeq_1643_);
lean_inc(v_toFunctor_1642_);
lean_dec(v_toApplicative_1638_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1699_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___f_1649_; lean_object* v___f_1650_; lean_object* v___f_1651_; lean_object* v___f_1652_; lean_object* v___x_1653_; lean_object* v___f_1654_; lean_object* v___f_1655_; lean_object* v___f_1656_; lean_object* v___x_1658_; 
v___f_1649_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1));
v___f_1650_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1642_);
v___f_1651_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1651_, 0, v_toFunctor_1642_);
v___f_1652_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1652_, 0, v_toFunctor_1642_);
v___x_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___f_1651_);
lean_ctor_set(v___x_1653_, 1, v___f_1652_);
v___f_1654_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1654_, 0, v_toSeqRight_1645_);
v___f_1655_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1655_, 0, v_toSeqLeft_1644_);
v___f_1656_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1656_, 0, v_toSeq_1643_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 4, v___f_1654_);
lean_ctor_set(v___x_1647_, 3, v___f_1655_);
lean_ctor_set(v___x_1647_, 2, v___f_1656_);
lean_ctor_set(v___x_1647_, 1, v___f_1649_);
lean_ctor_set(v___x_1647_, 0, v___x_1653_);
v___x_1658_ = v___x_1647_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v___f_1649_);
lean_ctor_set(v_reuseFailAlloc_1698_, 2, v___f_1656_);
lean_ctor_set(v_reuseFailAlloc_1698_, 3, v___f_1655_);
lean_ctor_set(v_reuseFailAlloc_1698_, 4, v___f_1654_);
v___x_1658_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v___f_1650_);
lean_ctor_set(v___x_1640_, 0, v___x_1658_);
v___x_1660_ = v___x_1640_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v___f_1650_);
v___x_1660_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1661_; lean_object* v_toApplicative_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1695_; 
v___x_1661_ = l_StateRefT_x27_instMonad___redArg(v___x_1660_);
v_toApplicative_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; 
v_unused_1696_ = lean_ctor_get(v___x_1661_, 1);
lean_dec(v_unused_1696_);
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1695_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_toApplicative_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1695_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_toFunctor_1666_; lean_object* v_toSeq_1667_; lean_object* v_toSeqLeft_1668_; lean_object* v_toSeqRight_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1693_; 
v_toFunctor_1666_ = lean_ctor_get(v_toApplicative_1662_, 0);
v_toSeq_1667_ = lean_ctor_get(v_toApplicative_1662_, 2);
v_toSeqLeft_1668_ = lean_ctor_get(v_toApplicative_1662_, 3);
v_toSeqRight_1669_ = lean_ctor_get(v_toApplicative_1662_, 4);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_toApplicative_1662_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; 
v_unused_1694_ = lean_ctor_get(v_toApplicative_1662_, 1);
lean_dec(v_unused_1694_);
v___x_1671_ = v_toApplicative_1662_;
v_isShared_1672_ = v_isSharedCheck_1693_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_toSeqRight_1669_);
lean_inc(v_toSeqLeft_1668_);
lean_inc(v_toSeq_1667_);
lean_inc(v_toFunctor_1666_);
lean_dec(v_toApplicative_1662_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1693_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___f_1673_; lean_object* v___f_1674_; lean_object* v___f_1675_; lean_object* v___f_1676_; lean_object* v___x_1677_; lean_object* v___f_1678_; lean_object* v___f_1679_; lean_object* v___f_1680_; lean_object* v___x_1682_; 
v___f_1673_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3));
v___f_1674_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1666_);
v___f_1675_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1675_, 0, v_toFunctor_1666_);
v___f_1676_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1676_, 0, v_toFunctor_1666_);
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___f_1675_);
lean_ctor_set(v___x_1677_, 1, v___f_1676_);
v___f_1678_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1678_, 0, v_toSeqRight_1669_);
v___f_1679_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1679_, 0, v_toSeqLeft_1668_);
v___f_1680_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1680_, 0, v_toSeq_1667_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 4, v___f_1678_);
lean_ctor_set(v___x_1671_, 3, v___f_1679_);
lean_ctor_set(v___x_1671_, 2, v___f_1680_);
lean_ctor_set(v___x_1671_, 1, v___f_1673_);
lean_ctor_set(v___x_1671_, 0, v___x_1677_);
v___x_1682_ = v___x_1671_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___f_1673_);
lean_ctor_set(v_reuseFailAlloc_1692_, 2, v___f_1680_);
lean_ctor_set(v_reuseFailAlloc_1692_, 3, v___f_1679_);
lean_ctor_set(v_reuseFailAlloc_1692_, 4, v___f_1678_);
v___x_1682_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1684_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v___f_1674_);
lean_ctor_set(v___x_1664_, 0, v___x_1682_);
v___x_1684_ = v___x_1664_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1682_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___f_1674_);
v___x_1684_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___f_1688_; lean_object* v___x_22923__overap_1689_; lean_object* v___x_1690_; 
v___x_1685_ = l_StateRefT_x27_instMonad___redArg(v___x_1684_);
v___x_1686_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
v___x_1687_ = l_instInhabitedOfMonad___redArg(v___x_1685_, v___x_1686_);
v___f_1688_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1688_, 0, v___x_1687_);
v___x_22923__overap_1689_ = lean_panic_fn_borrowed(v___f_1688_, v_msg_1628_);
lean_dec_ref(v___f_1688_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
v___x_1690_ = lean_apply_7(v___x_22923__overap_1689_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, lean_box(0));
return v___x_1690_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0___boxed(lean_object* v_msg_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v_msg_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(lean_object* v_x_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0___boxed(lean_object* v_x_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(v_x_1714_);
lean_dec(v_x_1714_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4(lean_object* v_params_1716_, lean_object* v_i_1717_){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v_type_1720_; 
v___x_1718_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0);
v___x_1719_ = lean_array_get_borrowed(v___x_1718_, v_params_1716_, v_i_1717_);
v_type_1720_ = lean_ctor_get(v___x_1719_, 2);
lean_inc_ref(v_type_1720_);
return v_type_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4___boxed(lean_object* v_params_1721_, lean_object* v_i_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4(v_params_1721_, v_i_1722_);
lean_dec(v_i_1722_);
lean_dec_ref(v_params_1721_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(lean_object* v_fvarId_1724_, lean_object* v_code_1725_, lean_object* v_fvarId_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
uint8_t v___x_1734_; 
v___x_1734_ = l_Lean_instBEqFVarId_beq(v_fvarId_1724_, v_fvarId_1726_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
lean_dec_ref(v_code_1725_);
v___x_1735_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1735_, 0, v_fvarId_1726_);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
else
{
lean_object* v___x_1737_; 
lean_dec(v_fvarId_1726_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v_code_1725_);
return v___x_1737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2___boxed(lean_object* v_fvarId_1738_, lean_object* v_code_1739_, lean_object* v_fvarId_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_1738_, v_code_1739_, v_fvarId_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v_fvarId_1738_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(lean_object* v_typeName_1749_, lean_object* v_a_1750_, lean_object* v_alts_1751_, lean_object* v_resultType_1752_, lean_object* v_discr_1753_, lean_object* v_code_1754_, lean_object* v_discr_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v_currDeclResultType_1763_; size_t v___x_1768_; size_t v___x_1769_; uint8_t v___x_1770_; 
v_currDeclResultType_1763_ = lean_ctor_get(v___y_1756_, 1);
v___x_1768_ = lean_ptr_addr(v_alts_1751_);
v___x_1769_ = lean_ptr_addr(v_a_1750_);
v___x_1770_ = lean_usize_dec_eq(v___x_1768_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_dec_ref(v_code_1754_);
goto v___jp_1764_;
}
else
{
size_t v___x_1771_; size_t v___x_1772_; uint8_t v___x_1773_; 
v___x_1771_ = lean_ptr_addr(v_resultType_1752_);
v___x_1772_ = lean_ptr_addr(v_currDeclResultType_1763_);
v___x_1773_ = lean_usize_dec_eq(v___x_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_dec_ref(v_code_1754_);
goto v___jp_1764_;
}
else
{
uint8_t v___x_1774_; 
v___x_1774_ = l_Lean_instBEqFVarId_beq(v_discr_1753_, v_discr_1755_);
if (v___x_1774_ == 0)
{
lean_dec_ref(v_code_1754_);
goto v___jp_1764_;
}
else
{
lean_object* v___x_1775_; 
lean_dec(v_discr_1755_);
lean_dec_ref(v_a_1750_);
lean_dec(v_typeName_1749_);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v_code_1754_);
return v___x_1775_;
}
}
}
v___jp_1764_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_inc_ref(v_currDeclResultType_1763_);
v___x_1765_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1765_, 0, v_typeName_1749_);
lean_ctor_set(v___x_1765_, 1, v_currDeclResultType_1763_);
lean_ctor_set(v___x_1765_, 2, v_discr_1755_);
lean_ctor_set(v___x_1765_, 3, v_a_1750_);
v___x_1766_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1___boxed(lean_object* v_typeName_1776_, lean_object* v_a_1777_, lean_object* v_alts_1778_, lean_object* v_resultType_1779_, lean_object* v_discr_1780_, lean_object* v_code_1781_, lean_object* v_discr_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_1776_, v_a_1777_, v_alts_1778_, v_resultType_1779_, v_discr_1780_, v_code_1781_, v_discr_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v_discr_1780_);
lean_dec_ref(v_resultType_1779_);
lean_dec_ref(v_alts_1778_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(lean_object* v_alt_1791_, lean_object* v_f_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___y_1801_; 
switch(lean_obj_tag(v_alt_1791_))
{
case 0:
{
lean_object* v_code_1820_; 
v_code_1820_ = lean_ctor_get(v_alt_1791_, 2);
lean_inc_ref(v_code_1820_);
v___y_1801_ = v_code_1820_;
goto v___jp_1800_;
}
case 1:
{
lean_object* v_code_1821_; 
v_code_1821_ = lean_ctor_get(v_alt_1791_, 1);
lean_inc_ref(v_code_1821_);
v___y_1801_ = v_code_1821_;
goto v___jp_1800_;
}
default: 
{
lean_object* v_code_1822_; 
v_code_1822_ = lean_ctor_get(v_alt_1791_, 0);
lean_inc_ref(v_code_1822_);
v___y_1801_ = v_code_1822_;
goto v___jp_1800_;
}
}
v___jp_1800_:
{
lean_object* v___x_1802_; 
lean_inc(v___y_1798_);
lean_inc_ref(v___y_1797_);
lean_inc(v___y_1796_);
lean_inc_ref(v___y_1795_);
lean_inc(v___y_1794_);
lean_inc_ref(v___y_1793_);
v___x_1802_ = lean_apply_8(v_f_1792_, v___y_1801_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, lean_box(0));
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1811_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1811_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1811_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1807_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1791_, v_a_1803_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1807_);
v___x_1809_ = v___x_1805_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec_ref(v_alt_1791_);
v_a_1812_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1802_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1802_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg___boxed(lean_object* v_alt_1823_, lean_object* v_f_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_alt_1823_, v_f_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(lean_object* v_fvarId_1833_, lean_object* v_i_1834_, lean_object* v_offset_1835_, lean_object* v_ty_1836_, lean_object* v_a_1837_, lean_object* v_y_1838_, lean_object* v_k_1839_, lean_object* v_code_1840_, lean_object* v_y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
size_t v___x_1849_; uint8_t v___x_1850_; 
v___x_1849_ = lean_ptr_addr(v_fvarId_1833_);
v___x_1850_ = lean_usize_dec_eq(v___x_1849_, v___x_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec_ref(v_code_1840_);
v___x_1851_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1851_, 0, v_fvarId_1833_);
lean_ctor_set(v___x_1851_, 1, v_i_1834_);
lean_ctor_set(v___x_1851_, 2, v_offset_1835_);
lean_ctor_set(v___x_1851_, 3, v_y_1841_);
lean_ctor_set(v___x_1851_, 4, v_ty_1836_);
lean_ctor_set(v___x_1851_, 5, v_a_1837_);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
else
{
uint8_t v___x_1853_; 
v___x_1853_ = lean_nat_dec_eq(v_i_1834_, v_i_1834_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
lean_dec_ref(v_code_1840_);
v___x_1854_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1854_, 0, v_fvarId_1833_);
lean_ctor_set(v___x_1854_, 1, v_i_1834_);
lean_ctor_set(v___x_1854_, 2, v_offset_1835_);
lean_ctor_set(v___x_1854_, 3, v_y_1841_);
lean_ctor_set(v___x_1854_, 4, v_ty_1836_);
lean_ctor_set(v___x_1854_, 5, v_a_1837_);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
else
{
uint8_t v___x_1856_; 
v___x_1856_ = lean_nat_dec_eq(v_offset_1835_, v_offset_1835_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
lean_dec_ref(v_code_1840_);
v___x_1857_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1857_, 0, v_fvarId_1833_);
lean_ctor_set(v___x_1857_, 1, v_i_1834_);
lean_ctor_set(v___x_1857_, 2, v_offset_1835_);
lean_ctor_set(v___x_1857_, 3, v_y_1841_);
lean_ctor_set(v___x_1857_, 4, v_ty_1836_);
lean_ctor_set(v___x_1857_, 5, v_a_1837_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
else
{
size_t v___x_1859_; size_t v___x_1860_; uint8_t v___x_1861_; 
v___x_1859_ = lean_ptr_addr(v_y_1838_);
v___x_1860_ = lean_ptr_addr(v_y_1841_);
v___x_1861_ = lean_usize_dec_eq(v___x_1859_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec_ref(v_code_1840_);
v___x_1862_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1862_, 0, v_fvarId_1833_);
lean_ctor_set(v___x_1862_, 1, v_i_1834_);
lean_ctor_set(v___x_1862_, 2, v_offset_1835_);
lean_ctor_set(v___x_1862_, 3, v_y_1841_);
lean_ctor_set(v___x_1862_, 4, v_ty_1836_);
lean_ctor_set(v___x_1862_, 5, v_a_1837_);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
return v___x_1863_;
}
else
{
size_t v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = lean_ptr_addr(v_ty_1836_);
v___x_1865_ = lean_usize_dec_eq(v___x_1864_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_dec_ref(v_code_1840_);
v___x_1866_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1866_, 0, v_fvarId_1833_);
lean_ctor_set(v___x_1866_, 1, v_i_1834_);
lean_ctor_set(v___x_1866_, 2, v_offset_1835_);
lean_ctor_set(v___x_1866_, 3, v_y_1841_);
lean_ctor_set(v___x_1866_, 4, v_ty_1836_);
lean_ctor_set(v___x_1866_, 5, v_a_1837_);
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
return v___x_1867_;
}
else
{
size_t v___x_1868_; size_t v___x_1869_; uint8_t v___x_1870_; 
v___x_1868_ = lean_ptr_addr(v_k_1839_);
v___x_1869_ = lean_ptr_addr(v_a_1837_);
v___x_1870_ = lean_usize_dec_eq(v___x_1868_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_dec_ref(v_code_1840_);
v___x_1871_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_1871_, 0, v_fvarId_1833_);
lean_ctor_set(v___x_1871_, 1, v_i_1834_);
lean_ctor_set(v___x_1871_, 2, v_offset_1835_);
lean_ctor_set(v___x_1871_, 3, v_y_1841_);
lean_ctor_set(v___x_1871_, 4, v_ty_1836_);
lean_ctor_set(v___x_1871_, 5, v_a_1837_);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; 
lean_dec(v_y_1841_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_ty_1836_);
lean_dec(v_offset_1835_);
lean_dec(v_i_1834_);
lean_dec(v_fvarId_1833_);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v_code_1840_);
return v___x_1873_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4___boxed(lean_object* v_fvarId_1874_, lean_object* v_i_1875_, lean_object* v_offset_1876_, lean_object* v_ty_1877_, lean_object* v_a_1878_, lean_object* v_y_1879_, lean_object* v_k_1880_, lean_object* v_code_1881_, lean_object* v_y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_1874_, v_i_1875_, v_offset_1876_, v_ty_1877_, v_a_1878_, v_y_1879_, v_k_1880_, v_code_1881_, v_y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec_ref(v_k_1880_);
lean_dec(v_y_1879_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(lean_object* v_fvarId_1891_, lean_object* v_i_1892_, lean_object* v_a_1893_, lean_object* v_y_1894_, lean_object* v_k_1895_, lean_object* v_code_1896_, lean_object* v_y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
size_t v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = lean_ptr_addr(v_fvarId_1891_);
v___x_1906_ = lean_usize_dec_eq(v___x_1905_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
lean_dec_ref(v_code_1896_);
v___x_1907_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1907_, 0, v_fvarId_1891_);
lean_ctor_set(v___x_1907_, 1, v_i_1892_);
lean_ctor_set(v___x_1907_, 2, v_y_1897_);
lean_ctor_set(v___x_1907_, 3, v_a_1893_);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
else
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_nat_dec_eq(v_i_1892_, v_i_1892_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
lean_dec_ref(v_code_1896_);
v___x_1910_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1910_, 0, v_fvarId_1891_);
lean_ctor_set(v___x_1910_, 1, v_i_1892_);
lean_ctor_set(v___x_1910_, 2, v_y_1897_);
lean_ctor_set(v___x_1910_, 3, v_a_1893_);
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
return v___x_1911_;
}
else
{
size_t v___x_1912_; size_t v___x_1913_; uint8_t v___x_1914_; 
v___x_1912_ = lean_ptr_addr(v_y_1894_);
v___x_1913_ = lean_ptr_addr(v_y_1897_);
v___x_1914_ = lean_usize_dec_eq(v___x_1912_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_dec_ref(v_code_1896_);
v___x_1915_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1915_, 0, v_fvarId_1891_);
lean_ctor_set(v___x_1915_, 1, v_i_1892_);
lean_ctor_set(v___x_1915_, 2, v_y_1897_);
lean_ctor_set(v___x_1915_, 3, v_a_1893_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
return v___x_1916_;
}
else
{
size_t v___x_1917_; size_t v___x_1918_; uint8_t v___x_1919_; 
v___x_1917_ = lean_ptr_addr(v_k_1895_);
v___x_1918_ = lean_ptr_addr(v_a_1893_);
v___x_1919_ = lean_usize_dec_eq(v___x_1917_, v___x_1918_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec_ref(v_code_1896_);
v___x_1920_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_1920_, 0, v_fvarId_1891_);
lean_ctor_set(v___x_1920_, 1, v_i_1892_);
lean_ctor_set(v___x_1920_, 2, v_y_1897_);
lean_ctor_set(v___x_1920_, 3, v_a_1893_);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
else
{
lean_object* v___x_1922_; 
lean_dec(v_y_1897_);
lean_dec_ref(v_a_1893_);
lean_dec(v_i_1892_);
lean_dec(v_fvarId_1891_);
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v_code_1896_);
return v___x_1922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3___boxed(lean_object* v_fvarId_1923_, lean_object* v_i_1924_, lean_object* v_a_1925_, lean_object* v_y_1926_, lean_object* v_k_1927_, lean_object* v_code_1928_, lean_object* v_y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_1923_, v_i_1924_, v_a_1925_, v_y_1926_, v_k_1927_, v_code_1928_, v_y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec_ref(v_k_1927_);
lean_dec(v_y_1926_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(lean_object* v_params_1938_, lean_object* v_i_1939_){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v_type_1942_; 
v___x_1940_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0);
v___x_1941_ = lean_array_get_borrowed(v___x_1940_, v_params_1938_, v_i_1939_);
v_type_1942_ = lean_ctor_get(v___x_1941_, 2);
lean_inc_ref(v_type_1942_);
return v_type_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed(lean_object* v_params_1943_, lean_object* v_i_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(v_params_1943_, v_i_1944_);
lean_dec(v_i_1944_);
lean_dec_ref(v_params_1943_);
return v_res_1945_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1(void){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1947_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1948_ = lean_unsigned_to_nat(44u);
v___x_1949_ = lean_unsigned_to_nat(353u);
v___x_1950_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_1951_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1952_ = l_mkPanicMessageWithDecl(v___x_1951_, v___x_1950_, v___x_1949_, v___x_1948_, v___x_1947_);
return v___x_1952_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3(void){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1954_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1955_ = lean_unsigned_to_nat(45u);
v___x_1956_ = lean_unsigned_to_nat(336u);
v___x_1957_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_1958_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1959_ = l_mkPanicMessageWithDecl(v___x_1958_, v___x_1957_, v___x_1956_, v___x_1955_, v___x_1954_);
return v___x_1959_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1960_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_1961_ = lean_unsigned_to_nat(45u);
v___x_1962_ = lean_unsigned_to_nat(341u);
v___x_1963_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
v___x_1964_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_1965_ = l_mkPanicMessageWithDecl(v___x_1964_, v___x_1963_, v___x_1962_, v___x_1961_, v___x_1960_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(lean_object* v_code_1966_, lean_object* v_decl_1967_, lean_object* v_k_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v_type_1995_; lean_object* v_value_1996_; lean_object* v___f_1997_; lean_object* v___x_1998_; 
v_type_1995_ = lean_ctor_get(v_decl_1967_, 2);
v_value_1996_ = lean_ctor_get(v_decl_1967_, 3);
lean_inc_n(v_value_1996_, 2);
v___f_1997_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2));
lean_inc_ref(v_type_1995_);
v___x_1998_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(v_type_1995_, v_value_1996_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; uint8_t v___x_2000_; lean_object* v___x_2001_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc_n(v_a_1999_, 2);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2000_ = 1;
v___x_2001_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_2000_, v_decl_1967_, v_a_1999_, v_value_1996_, v_a_1972_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2003_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
v___x_2003_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2479_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2006_ = v___x_2003_;
v_isShared_2007_ = v_isSharedCheck_2479_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2479_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v_value_2008_; lean_object* v___y_2010_; 
v_value_2008_ = lean_ctor_get(v_a_2002_, 3);
switch(lean_obj_tag(v_value_2008_))
{
case 4:
{
lean_object* v_args_2070_; lean_object* v___x_2071_; 
lean_del_object(v___x_2006_);
lean_dec(v_a_1999_);
v_args_2070_ = lean_ctor_get(v_value_2008_, 1);
v___x_2071_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2070_, v___f_1997_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v_fst_2073_; lean_object* v_snd_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v___x_2071_, 1);
v_fst_2073_ = lean_ctor_get(v_a_2072_, 0);
lean_inc(v_fst_2073_);
v_snd_2074_ = lean_ctor_get(v_a_2072_, 1);
lean_inc(v_snd_2074_);
lean_dec(v_a_2072_);
lean_inc_ref(v_value_2008_);
v___x_2075_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_value_2008_, v_fst_2073_);
v___x_2076_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2000_, v_a_2002_, v___x_2075_, v_a_1972_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2078_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2076_, 1);
v___x_2078_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(v_code_1966_, v_a_2077_, v_a_2004_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2087_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_2074_, v_a_2079_);
lean_dec(v_snd_2074_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2083_);
v___x_2085_ = v___x_2081_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_dec(v_snd_2074_);
return v___x_2078_;
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec(v_snd_2074_);
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v_a_2088_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2076_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2076_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec_ref(v_code_1966_);
v_a_2096_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2071_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2071_);
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
case 5:
{
lean_object* v_i_2104_; lean_object* v_args_2105_; uint8_t v___y_2107_; uint8_t v___x_2223_; 
v_i_2104_ = lean_ctor_get(v_value_2008_, 0);
v_args_2105_ = lean_ctor_get(v_value_2008_, 1);
v___x_2223_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_i_2104_);
if (v___x_2223_ == 0)
{
v___y_2107_ = v___x_2223_;
goto v___jp_2106_;
}
else
{
uint8_t v___x_2224_; 
v___x_2224_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_1999_);
v___y_2107_ = v___x_2224_;
goto v___jp_2106_;
}
v___jp_2106_:
{
if (v___y_2107_ == 0)
{
lean_object* v___x_2108_; 
lean_del_object(v___x_2006_);
lean_dec(v_a_1999_);
v___x_2108_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2105_, v___f_1997_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v_fst_2110_; lean_object* v_snd_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v_fst_2110_ = lean_ctor_get(v_a_2109_, 0);
lean_inc(v_fst_2110_);
v_snd_2111_ = lean_ctor_get(v_a_2109_, 1);
lean_inc(v_snd_2111_);
lean_dec(v_a_2109_);
lean_inc_ref(v_value_2008_);
v___x_2112_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_value_2008_, v_fst_2110_);
v___x_2113_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2000_, v_a_2002_, v___x_2112_, v_a_1972_);
if (lean_obj_tag(v___x_2113_) == 0)
{
if (lean_obj_tag(v_code_1966_) == 0)
{
lean_object* v_a_2114_; lean_object* v_decl_2115_; lean_object* v_k_2116_; size_t v___x_2117_; size_t v___x_2118_; uint8_t v___x_2119_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v_decl_2115_ = lean_ctor_get(v_code_1966_, 0);
v_k_2116_ = lean_ctor_get(v_code_1966_, 1);
v___x_2117_ = lean_ptr_addr(v_k_2116_);
v___x_2118_ = lean_ptr_addr(v_a_2004_);
v___x_2119_ = lean_usize_dec_eq(v___x_2117_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
v_isSharedCheck_2126_ = !lean_is_exclusive(v_code_1966_);
if (v_isSharedCheck_2126_ == 0)
{
lean_object* v_unused_2127_; lean_object* v_unused_2128_; 
v_unused_2127_ = lean_ctor_get(v_code_1966_, 1);
lean_dec(v_unused_2127_);
v_unused_2128_ = lean_ctor_get(v_code_1966_, 0);
lean_dec(v_unused_2128_);
v___x_2121_ = v_code_1966_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_dec(v_code_1966_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v_a_2004_);
lean_ctor_set(v___x_2121_, 0, v_a_2114_);
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2114_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_a_2004_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
v___y_1982_ = v_snd_2111_;
v___y_1983_ = v___x_2124_;
goto v___jp_1981_;
}
}
}
else
{
size_t v___x_2129_; size_t v___x_2130_; uint8_t v___x_2131_; 
v___x_2129_ = lean_ptr_addr(v_decl_2115_);
v___x_2130_ = lean_ptr_addr(v_a_2114_);
v___x_2131_ = lean_usize_dec_eq(v___x_2129_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
v_isSharedCheck_2138_ = !lean_is_exclusive(v_code_1966_);
if (v_isSharedCheck_2138_ == 0)
{
lean_object* v_unused_2139_; lean_object* v_unused_2140_; 
v_unused_2139_ = lean_ctor_get(v_code_1966_, 1);
lean_dec(v_unused_2139_);
v_unused_2140_ = lean_ctor_get(v_code_1966_, 0);
lean_dec(v_unused_2140_);
v___x_2133_ = v_code_1966_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_dec(v_code_1966_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 1, v_a_2004_);
lean_ctor_set(v___x_2133_, 0, v_a_2114_);
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2114_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_a_2004_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
v___y_1982_ = v_snd_2111_;
v___y_1983_ = v___x_2136_;
goto v___jp_1981_;
}
}
}
else
{
lean_dec(v_a_2114_);
lean_dec(v_a_2004_);
v___y_1982_ = v_snd_2111_;
v___y_1983_ = v_code_1966_;
goto v___jp_1981_;
}
}
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec_ref_known(v___x_2113_, 1);
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v___x_2141_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2142_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2141_);
v___y_1982_ = v_snd_2111_;
v___y_1983_ = v___x_2142_;
goto v___jp_1981_;
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_dec(v_snd_2111_);
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v_a_2143_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2113_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2113_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec_ref(v_code_1966_);
v_a_2151_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2108_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2108_);
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
else
{
lean_object* v_cidx_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v_cidx_2159_ = lean_ctor_get(v_i_2104_, 1);
v___x_2160_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_1999_, v_cidx_2159_);
lean_dec(v_a_1999_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2160_);
v___x_2162_ = v___x_2006_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2000_, v_a_2002_, v___x_2162_, v_a_1972_);
if (lean_obj_tag(v___x_2163_) == 0)
{
if (lean_obj_tag(v_code_1966_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2203_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2203_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2203_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v_decl_2168_; lean_object* v_k_2169_; size_t v___x_2170_; size_t v___x_2171_; uint8_t v___x_2172_; 
v_decl_2168_ = lean_ctor_get(v_code_1966_, 0);
v_k_2169_ = lean_ctor_get(v_code_1966_, 1);
v___x_2170_ = lean_ptr_addr(v_k_2169_);
v___x_2171_ = lean_ptr_addr(v_a_2004_);
v___x_2172_ = lean_usize_dec_eq(v___x_2170_, v___x_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2182_; 
v_isSharedCheck_2182_ = !lean_is_exclusive(v_code_1966_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; lean_object* v_unused_2184_; 
v_unused_2183_ = lean_ctor_get(v_code_1966_, 1);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_code_1966_, 0);
lean_dec(v_unused_2184_);
v___x_2174_ = v_code_1966_;
v_isShared_2175_ = v_isSharedCheck_2182_;
goto v_resetjp_2173_;
}
else
{
lean_dec(v_code_1966_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2182_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 1, v_a_2004_);
lean_ctor_set(v___x_2174_, 0, v_a_2164_);
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2164_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_a_2004_);
v___x_2177_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2179_; 
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2177_);
v___x_2179_ = v___x_2166_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
size_t v___x_2185_; size_t v___x_2186_; uint8_t v___x_2187_; 
v___x_2185_ = lean_ptr_addr(v_decl_2168_);
v___x_2186_ = lean_ptr_addr(v_a_2164_);
v___x_2187_ = lean_usize_dec_eq(v___x_2185_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2197_; 
v_isSharedCheck_2197_ = !lean_is_exclusive(v_code_1966_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; lean_object* v_unused_2199_; 
v_unused_2198_ = lean_ctor_get(v_code_1966_, 1);
lean_dec(v_unused_2198_);
v_unused_2199_ = lean_ctor_get(v_code_1966_, 0);
lean_dec(v_unused_2199_);
v___x_2189_ = v_code_1966_;
v_isShared_2190_ = v_isSharedCheck_2197_;
goto v_resetjp_2188_;
}
else
{
lean_dec(v_code_1966_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2197_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 1, v_a_2004_);
lean_ctor_set(v___x_2189_, 0, v_a_2164_);
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2164_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_a_2004_);
v___x_2192_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2194_; 
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2192_);
v___x_2194_ = v___x_2166_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v___x_2201_; 
lean_dec(v_a_2164_);
lean_dec(v_a_2004_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v_code_1966_);
v___x_2201_ = v___x_2166_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_code_1966_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
else
{
lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v___x_2163_, 0);
lean_dec(v_unused_2213_);
v___x_2205_ = v___x_2163_;
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
else
{
lean_dec(v___x_2163_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2207_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2208_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2207_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2208_);
v___x_2210_ = v___x_2205_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
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
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v_a_2214_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2163_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2163_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
}
}
case 6:
{
lean_inc_ref(v_value_2008_);
lean_del_object(v___x_2006_);
v___y_2010_ = v_a_1972_;
goto v___jp_2009_;
}
case 7:
{
lean_inc_ref(v_value_2008_);
lean_del_object(v___x_2006_);
v___y_2010_ = v_a_1972_;
goto v___jp_2009_;
}
case 9:
{
lean_object* v_fn_2225_; lean_object* v_args_2226_; lean_object* v___x_2227_; 
lean_del_object(v___x_2006_);
lean_dec(v_a_1999_);
v_fn_2225_ = lean_ctor_get(v_value_2008_, 0);
v_args_2226_ = lean_ctor_get(v_value_2008_, 1);
lean_inc(v_fn_2225_);
v___x_2227_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_2225_, v_a_1974_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2227_, 1);
if (lean_obj_tag(v_a_2228_) == 1)
{
lean_object* v_val_2229_; lean_object* v_type_2230_; lean_object* v_params_2231_; lean_object* v___f_2232_; lean_object* v___x_2233_; 
v_val_2229_ = lean_ctor_get(v_a_2228_, 0);
lean_inc(v_val_2229_);
lean_dec_ref_known(v_a_2228_, 1);
v_type_2230_ = lean_ctor_get(v_val_2229_, 2);
lean_inc_ref(v_type_2230_);
v_params_2231_ = lean_ctor_get(v_val_2229_, 3);
lean_inc_ref(v_params_2231_);
lean_dec(v_val_2229_);
v___f_2232_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__4___boxed), 2, 1);
lean_closure_set(v___f_2232_, 0, v_params_2231_);
v___x_2233_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2226_, v___f_2232_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v_fst_2235_; lean_object* v_snd_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
v_fst_2235_ = lean_ctor_get(v_a_2234_, 0);
lean_inc(v_fst_2235_);
v_snd_2236_ = lean_ctor_get(v_a_2234_, 1);
lean_inc(v_snd_2236_);
lean_dec(v_a_2234_);
lean_inc_ref(v_value_2008_);
v___x_2237_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_value_2008_, v_fst_2235_);
v___x_2238_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2000_, v_a_2002_, v___x_2237_, v_a_1972_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
v___x_2240_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(v_code_1966_, v_a_2239_, v_type_2230_, v_a_2004_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
lean_dec_ref(v_type_2230_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2249_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_2236_, v_a_2241_);
lean_dec(v_snd_2236_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2245_);
v___x_2247_ = v___x_2243_;
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
}
else
{
lean_dec(v_snd_2236_);
return v___x_2240_;
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec(v_snd_2236_);
lean_dec_ref(v_type_2230_);
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v_a_2250_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2238_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2238_);
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
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec_ref(v_type_2230_);
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec_ref(v_code_1966_);
v_a_2258_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2233_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2233_);
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
lean_dec(v_a_2228_);
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec_ref(v_code_1966_);
v___x_2266_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3);
v___x_2267_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2266_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
return v___x_2267_;
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec_ref(v_code_1966_);
v_a_2268_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2227_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2227_);
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
case 10:
{
lean_object* v_fn_2276_; lean_object* v_args_2277_; lean_object* v___x_2278_; 
lean_del_object(v___x_2006_);
lean_dec(v_a_1999_);
v_fn_2276_ = lean_ctor_get(v_value_2008_, 0);
v_args_2277_ = lean_ctor_get(v_value_2008_, 1);
lean_inc(v_fn_2276_);
v___x_2278_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_2276_, v_a_1974_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
if (lean_obj_tag(v_a_2279_) == 1)
{
lean_object* v_val_2280_; lean_object* v___x_2281_; 
v_val_2280_ = lean_ctor_get(v_a_2279_, 0);
lean_inc(v_val_2280_);
lean_dec_ref_known(v_a_2279_, 1);
v___x_2281_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(v_val_2280_, v_a_1974_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___y_2284_; uint8_t v___x_2336_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2336_ = lean_unbox(v_a_2282_);
lean_dec(v_a_2282_);
if (v___x_2336_ == 0)
{
lean_inc(v_fn_2276_);
v___y_2284_ = v_fn_2276_;
goto v___jp_2283_;
}
else
{
lean_object* v___x_2337_; 
lean_inc(v_fn_2276_);
v___x_2337_ = l_Lean_Compiler_LCNF_mkBoxedName(v_fn_2276_);
v___y_2284_ = v___x_2337_;
goto v___jp_2283_;
}
v___jp_2283_:
{
lean_object* v___x_2285_; 
v___x_2285_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2277_, v___f_1997_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v_fst_2287_; lean_object* v_snd_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v_fst_2287_ = lean_ctor_get(v_a_2286_, 0);
lean_inc(v_fst_2287_);
v_snd_2288_ = lean_ctor_get(v_a_2286_, 1);
lean_inc(v_snd_2288_);
lean_dec(v_a_2286_);
v___x_2289_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updatePapImp___redArg(v_value_2008_, v___y_2284_, v_fst_2287_);
v___x_2290_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2000_, v_a_2002_, v___x_2289_, v_a_1972_);
if (lean_obj_tag(v___x_2290_) == 0)
{
if (lean_obj_tag(v_code_1966_) == 0)
{
lean_object* v_a_2291_; lean_object* v_decl_2292_; lean_object* v_k_2293_; size_t v___x_2294_; size_t v___x_2295_; uint8_t v___x_2296_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2290_, 1);
v_decl_2292_ = lean_ctor_get(v_code_1966_, 0);
v_k_2293_ = lean_ctor_get(v_code_1966_, 1);
v___x_2294_ = lean_ptr_addr(v_k_2293_);
v___x_2295_ = lean_ptr_addr(v_a_2004_);
v___x_2296_ = lean_usize_dec_eq(v___x_2294_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
v_isSharedCheck_2303_ = !lean_is_exclusive(v_code_1966_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; lean_object* v_unused_2305_; 
v_unused_2304_ = lean_ctor_get(v_code_1966_, 1);
lean_dec(v_unused_2304_);
v_unused_2305_ = lean_ctor_get(v_code_1966_, 0);
lean_dec(v_unused_2305_);
v___x_2298_ = v_code_1966_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_dec(v_code_1966_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v_a_2004_);
lean_ctor_set(v___x_2298_, 0, v_a_2291_);
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2291_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_a_2004_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
v___y_1977_ = v_snd_2288_;
v___y_1978_ = v___x_2301_;
goto v___jp_1976_;
}
}
}
else
{
size_t v___x_2306_; size_t v___x_2307_; uint8_t v___x_2308_; 
v___x_2306_ = lean_ptr_addr(v_decl_2292_);
v___x_2307_ = lean_ptr_addr(v_a_2291_);
v___x_2308_ = lean_usize_dec_eq(v___x_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
v_isSharedCheck_2315_ = !lean_is_exclusive(v_code_1966_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; lean_object* v_unused_2317_; 
v_unused_2316_ = lean_ctor_get(v_code_1966_, 1);
lean_dec(v_unused_2316_);
v_unused_2317_ = lean_ctor_get(v_code_1966_, 0);
lean_dec(v_unused_2317_);
v___x_2310_ = v_code_1966_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_dec(v_code_1966_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 1, v_a_2004_);
lean_ctor_set(v___x_2310_, 0, v_a_2291_);
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2291_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_a_2004_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
v___y_1977_ = v_snd_2288_;
v___y_1978_ = v___x_2313_;
goto v___jp_1976_;
}
}
}
else
{
lean_dec(v_a_2291_);
lean_dec(v_a_2004_);
v___y_1977_ = v_snd_2288_;
v___y_1978_ = v_code_1966_;
goto v___jp_1976_;
}
}
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_dec_ref_known(v___x_2290_, 1);
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v___x_2318_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2319_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2318_);
v___y_1977_ = v_snd_2288_;
v___y_1978_ = v___x_2319_;
goto v___jp_1976_;
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v_snd_2288_);
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v_a_2320_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2290_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2290_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v___y_2284_);
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec_ref(v_code_1966_);
v_a_2328_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2285_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2285_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec_ref(v_code_1966_);
v_a_2338_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2281_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2281_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_dec(v_a_2279_);
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec_ref(v_code_1966_);
v___x_2346_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4);
v___x_2347_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2346_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
return v___x_2347_;
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec_ref(v_code_1966_);
v_a_2348_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2278_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2278_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
case 11:
{
lean_inc_ref(v_value_2008_);
lean_del_object(v___x_2006_);
v___y_2010_ = v_a_1972_;
goto v___jp_2009_;
}
case 12:
{
lean_object* v_args_2356_; lean_object* v___x_2357_; 
lean_del_object(v___x_2006_);
lean_dec(v_a_1999_);
v_args_2356_ = lean_ctor_get(v_value_2008_, 2);
v___x_2357_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2356_, v___f_1997_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v_fst_2359_; lean_object* v_snd_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
v_fst_2359_ = lean_ctor_get(v_a_2358_, 0);
lean_inc(v_fst_2359_);
v_snd_2360_ = lean_ctor_get(v_a_2358_, 1);
lean_inc(v_snd_2360_);
lean_dec(v_a_2358_);
lean_inc_ref(v_value_2008_);
v___x_2361_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___redArg(v_value_2008_, v_fst_2359_);
v___x_2362_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2000_, v_a_2002_, v___x_2361_, v_a_1972_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2401_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2401_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2401_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___y_2368_; 
if (lean_obj_tag(v_code_1966_) == 0)
{
lean_object* v_decl_2373_; lean_object* v_k_2374_; size_t v___x_2375_; size_t v___x_2376_; uint8_t v___x_2377_; 
v_decl_2373_ = lean_ctor_get(v_code_1966_, 0);
v_k_2374_ = lean_ctor_get(v_code_1966_, 1);
v___x_2375_ = lean_ptr_addr(v_k_2374_);
v___x_2376_ = lean_ptr_addr(v_a_2004_);
v___x_2377_ = lean_usize_dec_eq(v___x_2375_, v___x_2376_);
if (v___x_2377_ == 0)
{
lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
v_isSharedCheck_2384_ = !lean_is_exclusive(v_code_1966_);
if (v_isSharedCheck_2384_ == 0)
{
lean_object* v_unused_2385_; lean_object* v_unused_2386_; 
v_unused_2385_ = lean_ctor_get(v_code_1966_, 1);
lean_dec(v_unused_2385_);
v_unused_2386_ = lean_ctor_get(v_code_1966_, 0);
lean_dec(v_unused_2386_);
v___x_2379_ = v_code_1966_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_dec(v_code_1966_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 1, v_a_2004_);
lean_ctor_set(v___x_2379_, 0, v_a_2363_);
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2363_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v_a_2004_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
v___y_2368_ = v___x_2382_;
goto v___jp_2367_;
}
}
}
else
{
size_t v___x_2387_; size_t v___x_2388_; uint8_t v___x_2389_; 
v___x_2387_ = lean_ptr_addr(v_decl_2373_);
v___x_2388_ = lean_ptr_addr(v_a_2363_);
v___x_2389_ = lean_usize_dec_eq(v___x_2387_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
v_isSharedCheck_2396_ = !lean_is_exclusive(v_code_1966_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; lean_object* v_unused_2398_; 
v_unused_2397_ = lean_ctor_get(v_code_1966_, 1);
lean_dec(v_unused_2397_);
v_unused_2398_ = lean_ctor_get(v_code_1966_, 0);
lean_dec(v_unused_2398_);
v___x_2391_ = v_code_1966_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_dec(v_code_1966_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 1, v_a_2004_);
lean_ctor_set(v___x_2391_, 0, v_a_2363_);
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2363_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_a_2004_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
v___y_2368_ = v___x_2394_;
goto v___jp_2367_;
}
}
}
else
{
lean_dec(v_a_2363_);
lean_dec(v_a_2004_);
v___y_2368_ = v_code_1966_;
goto v___jp_2367_;
}
}
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_dec(v_a_2363_);
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v___x_2399_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2400_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2399_);
v___y_2368_ = v___x_2400_;
goto v___jp_2367_;
}
v___jp_2367_:
{
lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2369_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_2360_, v___y_2368_);
lean_dec(v_snd_2360_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2369_);
v___x_2371_ = v___x_2365_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec(v_snd_2360_);
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v_a_2402_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2362_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2362_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec_ref(v_code_1966_);
v_a_2410_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2357_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2357_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
case 13:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_del_object(v___x_2006_);
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1966_);
v___x_2418_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1);
v___x_2419_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2418_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
return v___x_2419_;
}
case 14:
{
lean_del_object(v___x_2006_);
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1966_);
v___y_1987_ = v_a_1969_;
v___y_1988_ = v_a_1970_;
v___y_1989_ = v_a_1971_;
v___y_1990_ = v_a_1972_;
v___y_1991_ = v_a_1973_;
v___y_1992_ = v_a_1974_;
goto v___jp_1986_;
}
case 15:
{
lean_del_object(v___x_2006_);
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1966_);
v___y_1987_ = v_a_1969_;
v___y_1988_ = v_a_1970_;
v___y_1989_ = v_a_1971_;
v___y_1990_ = v_a_1972_;
v___y_1991_ = v_a_1973_;
v___y_1992_ = v_a_1974_;
goto v___jp_1986_;
}
default: 
{
lean_object* v___x_2420_; 
lean_inc(v_value_2008_);
lean_del_object(v___x_2006_);
v___x_2420_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_2000_, v_a_2002_, v_a_1999_, v_value_2008_, v_a_1972_);
if (lean_obj_tag(v___x_2420_) == 0)
{
if (lean_obj_tag(v_code_1966_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2460_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2423_ = v___x_2420_;
v_isShared_2424_ = v_isSharedCheck_2460_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2420_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2460_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v_decl_2425_; lean_object* v_k_2426_; size_t v___x_2427_; size_t v___x_2428_; uint8_t v___x_2429_; 
v_decl_2425_ = lean_ctor_get(v_code_1966_, 0);
v_k_2426_ = lean_ctor_get(v_code_1966_, 1);
v___x_2427_ = lean_ptr_addr(v_k_2426_);
v___x_2428_ = lean_ptr_addr(v_a_2004_);
v___x_2429_ = lean_usize_dec_eq(v___x_2427_, v___x_2428_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2439_; 
v_isSharedCheck_2439_ = !lean_is_exclusive(v_code_1966_);
if (v_isSharedCheck_2439_ == 0)
{
lean_object* v_unused_2440_; lean_object* v_unused_2441_; 
v_unused_2440_ = lean_ctor_get(v_code_1966_, 1);
lean_dec(v_unused_2440_);
v_unused_2441_ = lean_ctor_get(v_code_1966_, 0);
lean_dec(v_unused_2441_);
v___x_2431_ = v_code_1966_;
v_isShared_2432_ = v_isSharedCheck_2439_;
goto v_resetjp_2430_;
}
else
{
lean_dec(v_code_1966_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2439_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 1, v_a_2004_);
lean_ctor_set(v___x_2431_, 0, v_a_2421_);
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2421_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_a_2004_);
v___x_2434_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2436_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2434_);
v___x_2436_ = v___x_2423_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
size_t v___x_2442_; size_t v___x_2443_; uint8_t v___x_2444_; 
v___x_2442_ = lean_ptr_addr(v_decl_2425_);
v___x_2443_ = lean_ptr_addr(v_a_2421_);
v___x_2444_ = lean_usize_dec_eq(v___x_2442_, v___x_2443_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2454_; 
v_isSharedCheck_2454_ = !lean_is_exclusive(v_code_1966_);
if (v_isSharedCheck_2454_ == 0)
{
lean_object* v_unused_2455_; lean_object* v_unused_2456_; 
v_unused_2455_ = lean_ctor_get(v_code_1966_, 1);
lean_dec(v_unused_2455_);
v_unused_2456_ = lean_ctor_get(v_code_1966_, 0);
lean_dec(v_unused_2456_);
v___x_2446_ = v_code_1966_;
v_isShared_2447_ = v_isSharedCheck_2454_;
goto v_resetjp_2445_;
}
else
{
lean_dec(v_code_1966_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2454_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 1, v_a_2004_);
lean_ctor_set(v___x_2446_, 0, v_a_2421_);
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2421_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_a_2004_);
v___x_2449_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2451_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2449_);
v___x_2451_ = v___x_2423_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v___x_2458_; 
lean_dec(v_a_2421_);
lean_dec(v_a_2004_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v_code_1966_);
v___x_2458_ = v___x_2423_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_code_1966_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
}
else
{
lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2469_ == 0)
{
lean_object* v_unused_2470_; 
v_unused_2470_ = lean_ctor_get(v___x_2420_, 0);
lean_dec(v_unused_2470_);
v___x_2462_ = v___x_2420_;
v_isShared_2463_ = v_isSharedCheck_2469_;
goto v_resetjp_2461_;
}
else
{
lean_dec(v___x_2420_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2469_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2464_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2465_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2464_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2465_);
v___x_2467_ = v___x_2462_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
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
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v_a_2471_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2420_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2420_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
v___jp_2009_:
{
lean_object* v___x_2011_; 
v___x_2011_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_2000_, v_a_2002_, v_a_1999_, v_value_2008_, v___y_2010_);
if (lean_obj_tag(v___x_2011_) == 0)
{
if (lean_obj_tag(v_code_1966_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2051_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2051_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2051_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_decl_2016_; lean_object* v_k_2017_; size_t v___x_2018_; size_t v___x_2019_; uint8_t v___x_2020_; 
v_decl_2016_ = lean_ctor_get(v_code_1966_, 0);
v_k_2017_ = lean_ctor_get(v_code_1966_, 1);
v___x_2018_ = lean_ptr_addr(v_k_2017_);
v___x_2019_ = lean_ptr_addr(v_a_2004_);
v___x_2020_ = lean_usize_dec_eq(v___x_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2030_; 
v_isSharedCheck_2030_ = !lean_is_exclusive(v_code_1966_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; lean_object* v_unused_2032_; 
v_unused_2031_ = lean_ctor_get(v_code_1966_, 1);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_code_1966_, 0);
lean_dec(v_unused_2032_);
v___x_2022_ = v_code_1966_;
v_isShared_2023_ = v_isSharedCheck_2030_;
goto v_resetjp_2021_;
}
else
{
lean_dec(v_code_1966_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2030_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 1, v_a_2004_);
lean_ctor_set(v___x_2022_, 0, v_a_2012_);
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2012_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_a_2004_);
v___x_2025_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2027_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2025_);
v___x_2027_ = v___x_2014_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
size_t v___x_2033_; size_t v___x_2034_; uint8_t v___x_2035_; 
v___x_2033_ = lean_ptr_addr(v_decl_2016_);
v___x_2034_ = lean_ptr_addr(v_a_2012_);
v___x_2035_ = lean_usize_dec_eq(v___x_2033_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2045_; 
v_isSharedCheck_2045_ = !lean_is_exclusive(v_code_1966_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; lean_object* v_unused_2047_; 
v_unused_2046_ = lean_ctor_get(v_code_1966_, 1);
lean_dec(v_unused_2046_);
v_unused_2047_ = lean_ctor_get(v_code_1966_, 0);
lean_dec(v_unused_2047_);
v___x_2037_ = v_code_1966_;
v_isShared_2038_ = v_isSharedCheck_2045_;
goto v_resetjp_2036_;
}
else
{
lean_dec(v_code_1966_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2045_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 1, v_a_2004_);
lean_ctor_set(v___x_2037_, 0, v_a_2012_);
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2012_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_a_2004_);
v___x_2040_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2042_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2040_);
v___x_2042_ = v___x_2014_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v___x_2049_; 
lean_dec(v_a_2012_);
lean_dec(v_a_2004_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v_code_1966_);
v___x_2049_ = v___x_2014_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_code_1966_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
else
{
lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2060_ == 0)
{
lean_object* v_unused_2061_; 
v_unused_2061_ = lean_ctor_get(v___x_2011_, 0);
lean_dec(v_unused_2061_);
v___x_2053_ = v___x_2011_;
v_isShared_2054_ = v_isSharedCheck_2060_;
goto v_resetjp_2052_;
}
else
{
lean_dec(v___x_2011_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2060_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2055_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
v___x_2056_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(v___x_2055_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2056_);
v___x_2058_ = v___x_2053_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_a_2004_);
lean_dec_ref(v_code_1966_);
v_a_2062_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2011_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2011_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2002_);
lean_dec(v_a_1999_);
lean_dec_ref(v_code_1966_);
return v___x_2003_;
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec(v_a_1999_);
lean_dec_ref(v_k_1968_);
lean_dec_ref(v_code_1966_);
v_a_2480_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2001_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2001_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
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
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v_value_1996_);
lean_dec_ref(v_k_1968_);
lean_dec_ref(v_decl_1967_);
lean_dec_ref(v_code_1966_);
v_a_2488_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_1998_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_1998_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
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
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___y_1982_, v___y_1983_);
lean_dec_ref(v___y_1982_);
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
return v___x_1985_;
}
v___jp_1986_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1);
v___x_1994_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_1993_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
return v___x_1994_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2497_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_2498_ = lean_unsigned_to_nat(44u);
v___x_2499_ = lean_unsigned_to_nat(284u);
v___x_2500_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0));
v___x_2501_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_2502_ = l_mkPanicMessageWithDecl(v___x_2501_, v___x_2500_, v___x_2499_, v___x_2498_, v___x_2497_);
return v___x_2502_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2503_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
v___x_2504_ = lean_unsigned_to_nat(59u);
v___x_2505_ = lean_unsigned_to_nat(287u);
v___x_2506_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0));
v___x_2507_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__0));
v___x_2508_ = l_mkPanicMessageWithDecl(v___x_2507_, v___x_2506_, v___x_2505_, v___x_2504_, v___x_2503_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(lean_object* v_code_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
switch(lean_obj_tag(v_code_2509_))
{
case 0:
{
lean_object* v_decl_2517_; lean_object* v_k_2518_; lean_object* v___x_2519_; 
v_decl_2517_ = lean_ctor_get(v_code_2509_, 0);
lean_inc_ref(v_decl_2517_);
v_k_2518_ = lean_ctor_get(v_code_2509_, 1);
lean_inc_ref(v_k_2518_);
v___x_2519_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(v_code_2509_, v_decl_2517_, v_k_2518_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
return v___x_2519_;
}
case 2:
{
lean_object* v_decl_2520_; lean_object* v_k_2521_; lean_object* v_params_2522_; lean_object* v_value_2523_; uint8_t v___x_2524_; lean_object* v___x_2525_; 
v_decl_2520_ = lean_ctor_get(v_code_2509_, 0);
v_k_2521_ = lean_ctor_get(v_code_2509_, 1);
v_params_2522_ = lean_ctor_get(v_decl_2520_, 2);
v_value_2523_ = lean_ctor_get(v_decl_2520_, 4);
v___x_2524_ = 1;
lean_inc_ref(v_value_2523_);
v___x_2525_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_value_2523_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v_currDeclResultType_2527_; lean_object* v___x_2528_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v_currDeclResultType_2527_ = lean_ctor_get(v_a_2510_, 1);
lean_inc_ref(v_params_2522_);
lean_inc_ref(v_currDeclResultType_2527_);
lean_inc_ref(v_decl_2520_);
v___x_2528_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2524_, v_decl_2520_, v_currDeclResultType_2527_, v_params_2522_, v_a_2526_, v_a_2513_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2530_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
lean_inc_ref(v_k_2521_);
v___x_2530_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2521_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2568_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2568_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2568_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
size_t v___x_2535_; size_t v___x_2536_; uint8_t v___x_2537_; 
v___x_2535_ = lean_ptr_addr(v_k_2521_);
v___x_2536_ = lean_ptr_addr(v_a_2531_);
v___x_2537_ = lean_usize_dec_eq(v___x_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2547_; 
v_isSharedCheck_2547_ = !lean_is_exclusive(v_code_2509_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; lean_object* v_unused_2549_; 
v_unused_2548_ = lean_ctor_get(v_code_2509_, 1);
lean_dec(v_unused_2548_);
v_unused_2549_ = lean_ctor_get(v_code_2509_, 0);
lean_dec(v_unused_2549_);
v___x_2539_ = v_code_2509_;
v_isShared_2540_ = v_isSharedCheck_2547_;
goto v_resetjp_2538_;
}
else
{
lean_dec(v_code_2509_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2547_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 1, v_a_2531_);
lean_ctor_set(v___x_2539_, 0, v_a_2529_);
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2529_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_a_2531_);
v___x_2542_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2544_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2542_);
v___x_2544_ = v___x_2533_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
else
{
size_t v___x_2550_; size_t v___x_2551_; uint8_t v___x_2552_; 
v___x_2550_ = lean_ptr_addr(v_decl_2520_);
v___x_2551_ = lean_ptr_addr(v_a_2529_);
v___x_2552_ = lean_usize_dec_eq(v___x_2550_, v___x_2551_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2562_; 
v_isSharedCheck_2562_ = !lean_is_exclusive(v_code_2509_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; lean_object* v_unused_2564_; 
v_unused_2563_ = lean_ctor_get(v_code_2509_, 1);
lean_dec(v_unused_2563_);
v_unused_2564_ = lean_ctor_get(v_code_2509_, 0);
lean_dec(v_unused_2564_);
v___x_2554_ = v_code_2509_;
v_isShared_2555_ = v_isSharedCheck_2562_;
goto v_resetjp_2553_;
}
else
{
lean_dec(v_code_2509_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2562_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 1, v_a_2531_);
lean_ctor_set(v___x_2554_, 0, v_a_2529_);
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2529_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_a_2531_);
v___x_2557_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2559_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2557_);
v___x_2559_ = v___x_2533_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
else
{
lean_object* v___x_2566_; 
lean_dec(v_a_2531_);
lean_dec(v_a_2529_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v_code_2509_);
v___x_2566_ = v___x_2533_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_code_2509_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
else
{
lean_dec(v_a_2529_);
lean_dec_ref_known(v_code_2509_, 2);
return v___x_2530_;
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec_ref_known(v_code_2509_, 2);
v_a_2569_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2528_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2528_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_2509_, 2);
return v___x_2525_;
}
}
case 3:
{
lean_object* v_fvarId_2577_; lean_object* v_args_2578_; uint8_t v___x_2579_; lean_object* v___x_2580_; 
v_fvarId_2577_ = lean_ctor_get(v_code_2509_, 0);
v_args_2578_ = lean_ctor_get(v_code_2509_, 1);
v___x_2579_ = 1;
v___x_2580_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_2579_, v_fvarId_2577_, v_a_2513_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2580_, 1);
if (lean_obj_tag(v_a_2581_) == 1)
{
lean_object* v_val_2582_; lean_object* v_params_2583_; lean_object* v___f_2584_; lean_object* v___x_2585_; 
v_val_2582_ = lean_ctor_get(v_a_2581_, 0);
lean_inc(v_val_2582_);
lean_dec_ref_known(v_a_2581_, 1);
v_params_2583_ = lean_ctor_get(v_val_2582_, 2);
lean_inc_ref(v_params_2583_);
lean_dec(v_val_2582_);
v___f_2584_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2584_, 0, v_params_2583_);
v___x_2585_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(v_args_2578_, v___f_2584_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2613_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2613_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2613_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v_fst_2590_; lean_object* v_snd_2591_; lean_object* v___y_2593_; uint8_t v___y_2599_; uint8_t v___x_2609_; 
v_fst_2590_ = lean_ctor_get(v_a_2586_, 0);
lean_inc(v_fst_2590_);
v_snd_2591_ = lean_ctor_get(v_a_2586_, 1);
lean_inc(v_snd_2591_);
lean_dec(v_a_2586_);
v___x_2609_ = l_Lean_instBEqFVarId_beq(v_fvarId_2577_, v_fvarId_2577_);
if (v___x_2609_ == 0)
{
v___y_2599_ = v___x_2609_;
goto v___jp_2598_;
}
else
{
size_t v___x_2610_; size_t v___x_2611_; uint8_t v___x_2612_; 
v___x_2610_ = lean_ptr_addr(v_args_2578_);
v___x_2611_ = lean_ptr_addr(v_fst_2590_);
v___x_2612_ = lean_usize_dec_eq(v___x_2610_, v___x_2611_);
v___y_2599_ = v___x_2612_;
goto v___jp_2598_;
}
v___jp_2592_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2594_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_2591_, v___y_2593_);
lean_dec(v_snd_2591_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2594_);
v___x_2596_ = v___x_2588_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
v___jp_2598_:
{
if (v___y_2599_ == 0)
{
lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_inc(v_fvarId_2577_);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_code_2509_);
if (v_isSharedCheck_2606_ == 0)
{
lean_object* v_unused_2607_; lean_object* v_unused_2608_; 
v_unused_2607_ = lean_ctor_get(v_code_2509_, 1);
lean_dec(v_unused_2607_);
v_unused_2608_ = lean_ctor_get(v_code_2509_, 0);
lean_dec(v_unused_2608_);
v___x_2601_ = v_code_2509_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_dec(v_code_2509_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 1, v_fst_2590_);
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_fvarId_2577_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_fst_2590_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
v___y_2593_ = v___x_2604_;
goto v___jp_2592_;
}
}
}
else
{
lean_dec(v_fst_2590_);
v___y_2593_ = v_code_2509_;
goto v___jp_2592_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec_ref_known(v_code_2509_, 2);
v_a_2614_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2585_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2585_);
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
else
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
lean_dec(v_a_2581_);
lean_dec_ref_known(v_code_2509_, 2);
v___x_2622_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1);
v___x_2623_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2622_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
return v___x_2623_;
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref_known(v_code_2509_, 2);
v_a_2624_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2580_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2580_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
case 4:
{
lean_object* v_cases_2632_; lean_object* v_typeName_2633_; lean_object* v_resultType_2634_; lean_object* v_discr_2635_; lean_object* v_alts_2636_; uint8_t v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v_cases_2632_ = lean_ctor_get(v_code_2509_, 0);
v_typeName_2633_ = lean_ctor_get(v_cases_2632_, 0);
lean_inc(v_typeName_2633_);
v_resultType_2634_ = lean_ctor_get(v_cases_2632_, 1);
lean_inc_ref(v_resultType_2634_);
v_discr_2635_ = lean_ctor_get(v_cases_2632_, 2);
lean_inc(v_discr_2635_);
v_alts_2636_ = lean_ctor_get(v_cases_2632_, 3);
lean_inc_ref_n(v_alts_2636_, 2);
v___x_2637_ = 1;
v___x_2638_ = lean_unsigned_to_nat(0u);
v___x_2639_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(v___x_2638_, v_alts_2636_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___x_2639_, 1);
v___x_2641_ = lean_box(0);
lean_inc(v_typeName_2633_);
v___x_2642_ = l_Lean_mkConst(v_typeName_2633_, v___x_2641_);
lean_inc(v_discr_2635_);
v___x_2643_ = l_Lean_Compiler_LCNF_getType(v_discr_2635_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; uint8_t v___x_2645_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2645_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2644_, v___x_2642_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; 
lean_inc_ref(v___x_2642_);
lean_inc(v_discr_2635_);
v___x_2646_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_discr_2635_, v_a_2644_, v___x_2642_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v___x_2648_ = lean_box(0);
v___x_2649_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2637_, v___x_2648_, v___x_2642_, v_a_2647_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v_fvarId_2651_; lean_object* v___x_2652_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
v_fvarId_2651_ = lean_ctor_get(v_a_2650_, 0);
lean_inc(v_fvarId_2651_);
v___x_2652_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_2633_, v_a_2640_, v_alts_2636_, v_resultType_2634_, v_discr_2635_, v_code_2509_, v_fvarId_2651_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec(v_discr_2635_);
lean_dec_ref(v_resultType_2634_);
lean_dec_ref(v_alts_2636_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2661_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2661_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2661_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2657_, 0, v_a_2650_);
lean_ctor_set(v___x_2657_, 1, v_a_2653_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2657_);
v___x_2659_ = v___x_2655_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
else
{
lean_dec(v_a_2650_);
return v___x_2652_;
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v_a_2640_);
lean_dec_ref(v_alts_2636_);
lean_dec(v_discr_2635_);
lean_dec_ref(v_resultType_2634_);
lean_dec(v_typeName_2633_);
lean_dec_ref_known(v_code_2509_, 1);
v_a_2662_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2649_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2649_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec_ref(v___x_2642_);
lean_dec(v_a_2640_);
lean_dec_ref(v_alts_2636_);
lean_dec(v_discr_2635_);
lean_dec_ref(v_resultType_2634_);
lean_dec(v_typeName_2633_);
lean_dec_ref_known(v_code_2509_, 1);
v_a_2670_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2646_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2646_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
else
{
lean_object* v___x_2678_; 
lean_dec(v_a_2644_);
lean_dec_ref(v___x_2642_);
lean_inc(v_discr_2635_);
v___x_2678_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(v_typeName_2633_, v_a_2640_, v_alts_2636_, v_resultType_2634_, v_discr_2635_, v_code_2509_, v_discr_2635_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec(v_discr_2635_);
lean_dec_ref(v_resultType_2634_);
lean_dec_ref(v_alts_2636_);
return v___x_2678_;
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec_ref(v___x_2642_);
lean_dec(v_a_2640_);
lean_dec_ref(v_alts_2636_);
lean_dec(v_discr_2635_);
lean_dec_ref(v_resultType_2634_);
lean_dec(v_typeName_2633_);
lean_dec_ref_known(v_code_2509_, 1);
v_a_2679_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2643_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2643_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref(v_alts_2636_);
lean_dec(v_discr_2635_);
lean_dec_ref(v_resultType_2634_);
lean_dec(v_typeName_2633_);
lean_dec_ref_known(v_code_2509_, 1);
v_a_2687_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2639_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2639_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_2695_; lean_object* v_currDeclResultType_2696_; lean_object* v___x_2697_; 
v_fvarId_2695_ = lean_ctor_get(v_code_2509_, 0);
lean_inc_n(v_fvarId_2695_, 2);
v_currDeclResultType_2696_ = lean_ctor_get(v_a_2510_, 1);
v___x_2697_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2695_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; uint8_t v___x_2699_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2699_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2698_, v_currDeclResultType_2696_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; 
lean_inc_ref(v_currDeclResultType_2696_);
lean_inc(v_fvarId_2695_);
v___x_2700_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_fvarId_2695_, v_a_2698_, v_currDeclResultType_2696_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; uint8_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
lean_dec_ref_known(v___x_2700_, 1);
v___x_2702_ = 1;
v___x_2703_ = lean_box(0);
lean_inc_ref(v_currDeclResultType_2696_);
v___x_2704_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2702_, v___x_2703_, v_currDeclResultType_2696_, v_a_2701_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v_fvarId_2706_; lean_object* v___x_2707_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2704_, 1);
v_fvarId_2706_ = lean_ctor_get(v_a_2705_, 0);
lean_inc(v_fvarId_2706_);
v___x_2707_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_2695_, v_code_2509_, v_fvarId_2706_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec(v_fvarId_2695_);
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
lean_dec_ref_known(v_code_2509_, 1);
lean_dec(v_fvarId_2695_);
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
lean_dec_ref_known(v_code_2509_, 1);
lean_dec(v_fvarId_2695_);
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
lean_inc(v_fvarId_2695_);
v___x_2733_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(v_fvarId_2695_, v_code_2509_, v_fvarId_2695_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec(v_fvarId_2695_);
return v___x_2733_;
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec_ref_known(v_code_2509_, 1);
lean_dec(v_fvarId_2695_);
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
case 6:
{
lean_object* v_type_2742_; lean_object* v_currDeclResultType_2743_; size_t v___x_2744_; size_t v___x_2745_; uint8_t v___x_2746_; 
v_type_2742_ = lean_ctor_get(v_code_2509_, 0);
v_currDeclResultType_2743_ = lean_ctor_get(v_a_2510_, 1);
v___x_2744_ = lean_ptr_addr(v_type_2742_);
v___x_2745_ = lean_ptr_addr(v_currDeclResultType_2743_);
v___x_2746_ = lean_usize_dec_eq(v___x_2744_, v___x_2745_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2754_; 
v_isSharedCheck_2754_ = !lean_is_exclusive(v_code_2509_);
if (v_isSharedCheck_2754_ == 0)
{
lean_object* v_unused_2755_; 
v_unused_2755_ = lean_ctor_get(v_code_2509_, 0);
lean_dec(v_unused_2755_);
v___x_2748_ = v_code_2509_;
v_isShared_2749_ = v_isSharedCheck_2754_;
goto v_resetjp_2747_;
}
else
{
lean_dec(v_code_2509_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2754_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
lean_inc_ref(v_currDeclResultType_2743_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v_currDeclResultType_2743_);
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_currDeclResultType_2743_);
v___x_2751_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_object* v___x_2752_; 
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
return v___x_2752_;
}
}
}
else
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2756_, 0, v_code_2509_);
return v___x_2756_;
}
}
case 8:
{
lean_object* v_fvarId_2757_; lean_object* v_i_2758_; lean_object* v_y_2759_; lean_object* v_k_2760_; lean_object* v___x_2761_; 
v_fvarId_2757_ = lean_ctor_get(v_code_2509_, 0);
lean_inc(v_fvarId_2757_);
v_i_2758_ = lean_ctor_get(v_code_2509_, 1);
lean_inc(v_i_2758_);
v_y_2759_ = lean_ctor_get(v_code_2509_, 2);
lean_inc(v_y_2759_);
v_k_2760_ = lean_ctor_get(v_code_2509_, 3);
lean_inc_ref_n(v_k_2760_, 2);
v___x_2761_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2760_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
v___x_2763_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11);
lean_inc(v_y_2759_);
v___x_2764_ = l_Lean_Compiler_LCNF_getType(v_y_2759_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; uint8_t v___x_2766_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
v___x_2766_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2765_, v___x_2763_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; 
lean_inc(v_y_2759_);
v___x_2767_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_y_2759_, v_a_2765_, v___x_2763_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; uint8_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2769_ = 1;
v___x_2770_ = lean_box(0);
v___x_2771_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2769_, v___x_2770_, v___x_2763_, v_a_2768_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v_fvarId_2773_; lean_object* v___x_2774_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
v_fvarId_2773_ = lean_ctor_get(v_a_2772_, 0);
lean_inc(v_fvarId_2773_);
v___x_2774_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_2757_, v_i_2758_, v_a_2762_, v_y_2759_, v_k_2760_, v_code_2509_, v_fvarId_2773_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec_ref(v_k_2760_);
lean_dec(v_y_2759_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2783_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2783_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2783_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2779_, 0, v_a_2772_);
lean_ctor_set(v___x_2779_, 1, v_a_2775_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2779_);
v___x_2781_ = v___x_2777_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
else
{
lean_dec(v_a_2772_);
return v___x_2774_;
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v_a_2762_);
lean_dec_ref(v_k_2760_);
lean_dec(v_y_2759_);
lean_dec(v_i_2758_);
lean_dec(v_fvarId_2757_);
lean_dec_ref_known(v_code_2509_, 4);
v_a_2784_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2771_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2771_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec(v_a_2762_);
lean_dec_ref(v_k_2760_);
lean_dec(v_y_2759_);
lean_dec(v_i_2758_);
lean_dec(v_fvarId_2757_);
lean_dec_ref_known(v_code_2509_, 4);
v_a_2792_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2767_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2767_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
else
{
lean_object* v___x_2800_; 
lean_dec(v_a_2765_);
lean_inc(v_y_2759_);
v___x_2800_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(v_fvarId_2757_, v_i_2758_, v_a_2762_, v_y_2759_, v_k_2760_, v_code_2509_, v_y_2759_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec_ref(v_k_2760_);
lean_dec(v_y_2759_);
return v___x_2800_;
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2762_);
lean_dec_ref(v_k_2760_);
lean_dec(v_y_2759_);
lean_dec(v_i_2758_);
lean_dec(v_fvarId_2757_);
lean_dec_ref_known(v_code_2509_, 4);
v_a_2801_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2764_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2764_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_dec_ref(v_k_2760_);
lean_dec(v_y_2759_);
lean_dec(v_i_2758_);
lean_dec(v_fvarId_2757_);
lean_dec_ref_known(v_code_2509_, 4);
return v___x_2761_;
}
}
case 9:
{
lean_object* v_fvarId_2809_; lean_object* v_i_2810_; lean_object* v_offset_2811_; lean_object* v_y_2812_; lean_object* v_ty_2813_; lean_object* v_k_2814_; lean_object* v___x_2815_; 
v_fvarId_2809_ = lean_ctor_get(v_code_2509_, 0);
lean_inc(v_fvarId_2809_);
v_i_2810_ = lean_ctor_get(v_code_2509_, 1);
lean_inc(v_i_2810_);
v_offset_2811_ = lean_ctor_get(v_code_2509_, 2);
lean_inc(v_offset_2811_);
v_y_2812_ = lean_ctor_get(v_code_2509_, 3);
lean_inc(v_y_2812_);
v_ty_2813_ = lean_ctor_get(v_code_2509_, 4);
lean_inc_ref(v_ty_2813_);
v_k_2814_ = lean_ctor_get(v_code_2509_, 5);
lean_inc_ref_n(v_k_2814_, 2);
v___x_2815_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_k_2814_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2817_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
lean_inc(v_y_2812_);
v___x_2817_ = l_Lean_Compiler_LCNF_getType(v_y_2812_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; uint8_t v___x_2819_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2817_, 1);
v___x_2819_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(v_a_2818_, v_ty_2813_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; 
lean_inc_ref(v_ty_2813_);
lean_inc(v_y_2812_);
v___x_2820_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(v_y_2812_, v_a_2818_, v_ty_2813_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = 1;
v___x_2823_ = lean_box(0);
lean_inc_ref(v_ty_2813_);
v___x_2824_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2822_, v___x_2823_, v_ty_2813_, v_a_2821_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v_fvarId_2826_; lean_object* v___x_2827_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
v_fvarId_2826_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_fvarId_2826_);
v___x_2827_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_2809_, v_i_2810_, v_offset_2811_, v_ty_2813_, v_a_2816_, v_y_2812_, v_k_2814_, v_code_2509_, v_fvarId_2826_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec_ref(v_k_2814_);
lean_dec(v_y_2812_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2836_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2836_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2836_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2832_, 0, v_a_2825_);
lean_ctor_set(v___x_2832_, 1, v_a_2828_);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2832_);
v___x_2834_ = v___x_2830_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
else
{
lean_dec(v_a_2825_);
return v___x_2827_;
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec(v_a_2816_);
lean_dec_ref(v_k_2814_);
lean_dec_ref(v_ty_2813_);
lean_dec(v_y_2812_);
lean_dec(v_offset_2811_);
lean_dec(v_i_2810_);
lean_dec_ref_known(v_code_2509_, 6);
lean_dec(v_fvarId_2809_);
v_a_2837_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2824_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2824_);
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
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec(v_a_2816_);
lean_dec_ref(v_k_2814_);
lean_dec_ref(v_ty_2813_);
lean_dec(v_y_2812_);
lean_dec(v_offset_2811_);
lean_dec(v_i_2810_);
lean_dec_ref_known(v_code_2509_, 6);
lean_dec(v_fvarId_2809_);
v_a_2845_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2820_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2820_);
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
else
{
lean_object* v___x_2853_; 
lean_dec(v_a_2818_);
lean_inc(v_y_2812_);
v___x_2853_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(v_fvarId_2809_, v_i_2810_, v_offset_2811_, v_ty_2813_, v_a_2816_, v_y_2812_, v_k_2814_, v_code_2509_, v_y_2812_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec_ref(v_k_2814_);
lean_dec(v_y_2812_);
return v___x_2853_;
}
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec(v_a_2816_);
lean_dec_ref(v_k_2814_);
lean_dec_ref(v_ty_2813_);
lean_dec(v_y_2812_);
lean_dec(v_offset_2811_);
lean_dec(v_i_2810_);
lean_dec_ref_known(v_code_2509_, 6);
lean_dec(v_fvarId_2809_);
v_a_2854_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2817_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2817_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
else
{
lean_dec_ref(v_k_2814_);
lean_dec_ref(v_ty_2813_);
lean_dec(v_y_2812_);
lean_dec(v_offset_2811_);
lean_dec(v_i_2810_);
lean_dec(v_fvarId_2809_);
lean_dec_ref_known(v_code_2509_, 6);
return v___x_2815_;
}
}
default: 
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
lean_dec_ref(v_code_2509_);
v___x_2862_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2);
v___x_2863_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(v___x_2862_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
return v___x_2863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed(lean_object* v_code_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_code_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(lean_object* v_i_2873_, lean_object* v_as_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2882_; uint8_t v___x_2883_; 
v___x_2882_ = lean_array_get_size(v_as_2874_);
v___x_2883_ = lean_nat_dec_lt(v_i_2873_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; 
lean_dec(v_i_2873_);
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v_as_2874_);
return v___x_2884_;
}
else
{
lean_object* v___f_2885_; lean_object* v_a_2886_; lean_object* v___x_2887_; 
v___f_2885_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed), 8, 0);
v_a_2886_ = lean_array_fget_borrowed(v_as_2874_, v_i_2873_);
lean_inc(v_a_2886_);
v___x_2887_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_a_2886_, v___f_2885_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; size_t v___x_2889_; size_t v___x_2890_; uint8_t v___x_2891_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v___x_2889_ = lean_ptr_addr(v_a_2886_);
v___x_2890_ = lean_ptr_addr(v_a_2888_);
v___x_2891_ = lean_usize_dec_eq(v___x_2889_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = lean_nat_add(v_i_2873_, v___x_2892_);
v___x_2894_ = lean_array_fset(v_as_2874_, v_i_2873_, v_a_2888_);
lean_dec(v_i_2873_);
v_i_2873_ = v___x_2893_;
v_as_2874_ = v___x_2894_;
goto _start;
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
lean_dec(v_a_2888_);
v___x_2896_ = lean_unsigned_to_nat(1u);
v___x_2897_ = lean_nat_add(v_i_2873_, v___x_2896_);
lean_dec(v_i_2873_);
v_i_2873_ = v___x_2897_;
goto _start;
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec_ref(v_as_2874_);
lean_dec(v_i_2873_);
v_a_2899_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2887_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2887_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3___boxed(lean_object* v_i_2907_, lean_object* v_as_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(v_i_2907_, v_as_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___boxed(lean_object* v_code_2917_, lean_object* v_decl_2918_, lean_object* v_k_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(v_code_2917_, v_decl_2918_, v_k_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_);
lean_dec(v_a_2925_);
lean_dec_ref(v_a_2924_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(uint8_t v_pu_2928_, lean_object* v_alt_2929_, lean_object* v_f_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(v_alt_2929_, v_f_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___boxed(lean_object* v_pu_2939_, lean_object* v_alt_2940_, lean_object* v_f_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
uint8_t v_pu_boxed_2949_; lean_object* v_res_2950_; 
v_pu_boxed_2949_ = lean_unbox(v_pu_2939_);
v_res_2950_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(v_pu_boxed_2949_, v_alt_2940_, v_f_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(lean_object* v_as_2954_, size_t v_i_2955_, size_t v_stop_2956_, lean_object* v_b_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_a_2964_; uint8_t v___x_2968_; 
v___x_2968_ = lean_usize_dec_eq(v_i_2955_, v_stop_2956_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; lean_object* v_value_2970_; 
v___x_2969_ = lean_array_uget(v_as_2954_, v_i_2955_);
v_value_2970_ = lean_ctor_get(v___x_2969_, 1);
lean_inc_ref(v_value_2970_);
if (lean_obj_tag(v_value_2970_) == 0)
{
lean_object* v_toSignature_2971_; uint8_t v_recursive_2972_; lean_object* v_inlineAttr_x3f_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3018_; 
v_toSignature_2971_ = lean_ctor_get(v___x_2969_, 0);
v_recursive_2972_ = lean_ctor_get_uint8(v___x_2969_, sizeof(void*)*3);
v_inlineAttr_x3f_2973_ = lean_ctor_get(v___x_2969_, 2);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; 
v_unused_3019_ = lean_ctor_get(v___x_2969_, 1);
lean_dec(v_unused_3019_);
v___x_2975_ = v___x_2969_;
v_isShared_2976_ = v_isSharedCheck_3018_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_inlineAttr_x3f_2973_);
lean_inc(v_toSignature_2971_);
lean_dec(v___x_2969_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3018_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v_code_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3017_; 
v_code_2977_ = lean_ctor_get(v_value_2970_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_value_2970_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_2979_ = v_value_2970_;
v_isShared_2980_ = v_isSharedCheck_3017_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_code_2977_);
lean_dec(v_value_2970_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3017_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v_name_2981_; lean_object* v_type_2982_; lean_object* v_s_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v_name_2981_ = lean_ctor_get(v_toSignature_2971_, 0);
v_type_2982_ = lean_ctor_get(v_toSignature_2971_, 2);
lean_inc_ref(v_type_2982_);
lean_inc(v_name_2981_);
v_s_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_2983_, 0, v_name_2981_);
lean_ctor_set(v_s_2983_, 1, v_type_2982_);
v___x_2984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0));
v___x_2985_ = lean_st_mk_ref(v___x_2984_);
v___x_2986_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(v_code_2977_, v_s_2983_, v___x_2985_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec_ref_known(v_s_2983_, 2);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2988_; lean_object* v_auxDecls_2989_; lean_object* v___x_2990_; uint8_t v___x_2991_; lean_object* v___x_2993_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2986_, 1);
v___x_2988_ = lean_st_ref_get(v___x_2985_);
lean_dec(v___x_2985_);
v_auxDecls_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc_ref(v_auxDecls_2989_);
lean_dec(v___x_2988_);
v___x_2990_ = l_Array_append___redArg(v_b_2957_, v_auxDecls_2989_);
lean_dec_ref(v_auxDecls_2989_);
v___x_2991_ = 1;
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 0, v_a_2987_);
v___x_2993_ = v___x_2979_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_2987_);
v___x_2993_ = v_reuseFailAlloc_3008_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2995_; 
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 1, v___x_2993_);
v___x_2995_ = v___x_2975_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_toSignature_2971_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_3007_, 2, v_inlineAttr_x3f_2973_);
lean_ctor_set_uint8(v_reuseFailAlloc_3007_, sizeof(void*)*3, v_recursive_2972_);
v___x_2995_ = v_reuseFailAlloc_3007_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_2991_, v___x_2995_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2998_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v___x_2998_ = lean_array_push(v___x_2990_, v_a_2997_);
v_a_2964_ = v___x_2998_;
goto v___jp_2963_;
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref(v___x_2990_);
v_a_2999_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2996_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2996_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec(v___x_2985_);
lean_del_object(v___x_2979_);
lean_del_object(v___x_2975_);
lean_dec(v_inlineAttr_x3f_2973_);
lean_dec_ref(v_toSignature_2971_);
lean_dec_ref(v_b_2957_);
v_a_3009_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2986_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2986_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
}
}
else
{
lean_object* v___x_3020_; 
lean_dec_ref_known(v_value_2970_, 1);
v___x_3020_ = lean_array_push(v_b_2957_, v___x_2969_);
v_a_2964_ = v___x_3020_;
goto v___jp_2963_;
}
}
else
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_b_2957_);
return v___x_3021_;
}
v___jp_2963_:
{
size_t v___x_2965_; size_t v___x_2966_; 
v___x_2965_ = ((size_t)1ULL);
v___x_2966_ = lean_usize_add(v_i_2955_, v___x_2965_);
v_i_2955_ = v___x_2966_;
v_b_2957_ = v_a_2964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___boxed(lean_object* v_as_3022_, lean_object* v_i_3023_, lean_object* v_stop_3024_, lean_object* v_b_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
size_t v_i_boxed_3031_; size_t v_stop_boxed_3032_; lean_object* v_res_3033_; 
v_i_boxed_3031_ = lean_unbox_usize(v_i_3023_);
lean_dec(v_i_3023_);
v_stop_boxed_3032_ = lean_unbox_usize(v_stop_3024_);
lean_dec(v_stop_3024_);
v_res_3033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_as_3022_, v_i_boxed_3031_, v_stop_boxed_3032_, v_b_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v_as_3022_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(lean_object* v_decls_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v___y_3041_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3044_ = lean_unsigned_to_nat(0u);
v___x_3045_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0));
v___x_3046_ = lean_array_get_size(v_decls_3034_);
v___x_3047_ = lean_nat_dec_lt(v___x_3044_, v___x_3046_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_Compiler_LCNF_addBoxedVersions(v___x_3045_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3048_;
}
else
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_nat_dec_le(v___x_3046_, v___x_3046_);
if (v___x_3049_ == 0)
{
if (v___x_3047_ == 0)
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lean_Compiler_LCNF_addBoxedVersions(v___x_3045_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3050_;
}
else
{
size_t v___x_3051_; size_t v___x_3052_; lean_object* v___x_3053_; 
v___x_3051_ = ((size_t)0ULL);
v___x_3052_ = lean_usize_of_nat(v___x_3046_);
v___x_3053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_decls_3034_, v___x_3051_, v___x_3052_, v___x_3045_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
v___y_3041_ = v___x_3053_;
goto v___jp_3040_;
}
}
else
{
size_t v___x_3054_; size_t v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = ((size_t)0ULL);
v___x_3055_ = lean_usize_of_nat(v___x_3046_);
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(v_decls_3034_, v___x_3054_, v___x_3055_, v___x_3045_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
v___y_3041_ = v___x_3056_;
goto v___jp_3040_;
}
}
v___jp_3040_:
{
if (lean_obj_tag(v___y_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3043_; 
v_a_3042_ = lean_ctor_get(v___y_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref_known(v___y_3041_, 1);
v___x_3043_ = l_Lean_Compiler_LCNF_addBoxedVersions(v_a_3042_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3043_;
}
else
{
return v___y_3041_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run___boxed(lean_object* v_decls_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(v_decls_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
lean_dec_ref(v_decls_3057_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3145_; uint8_t v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3145_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_));
v___x_3146_ = 1;
v___x_3147_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_));
v___x_3148_ = l_Lean_registerTraceClass(v___x_3145_, v___x_3146_, v___x_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2____boxed(lean_object* v_a_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_();
return v_res_3150_;
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
