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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Expr_isVoid(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(lean_object*, size_t, size_t);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_closureMaxArgs;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "boxed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "res"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 61, 90, 23, 143, 26, 140, 228)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__3_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4_value;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addBoxedVersions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addBoxedVersions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1_value;
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1_value;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateLetImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2_value;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3_value;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
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
extern lean_object* l_Lean_maxSmallNat;
lean_object* l_Lean_Compiler_LCNF_CtorInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_CtorInfo_isScalar(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updatePapImp(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "_private.Lean.Compiler.LCNF.ExplicitBoxing.0.Lean.Compiler.LCNF.Code.explicitBoxing"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_16; 
x_5 = lean_array_uget_borrowed(x_1, x_2);
x_6 = lean_ctor_get(x_5, 2);
x_7 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_8 = 1;
x_16 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(x_6);
if (x_16 == 0)
{
x_9 = x_7;
goto block_15;
}
else
{
x_9 = x_16;
goto block_15;
}
block_15:
{
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 2);
x_11 = l_Lean_Expr_isVoid(x_10);
if (x_11 == 0)
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
goto _start;
}
else
{
return x_8;
}
}
else
{
return x_8;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_7);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = x_19;
goto block_16;
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_26; 
x_20 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_20);
lean_dec(x_4);
x_26 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(x_6);
lean_dec_ref(x_6);
if (x_26 == 0)
{
if (x_19 == 0)
{
x_21 = x_26;
goto block_25;
}
else
{
if (x_19 == 0)
{
x_21 = x_26;
goto block_25;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_18);
x_29 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion_spec__0(x_7, x_27, x_28);
x_21 = x_29;
goto block_25;
}
}
}
else
{
x_21 = x_26;
goto block_25;
}
block_25:
{
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_isExtern(x_20, x_5);
x_8 = x_22;
goto block_16;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_20);
lean_dec_ref(x_7);
lean_dec(x_5);
x_23 = lean_box(x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
block_16:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_closureMaxArgs;
x_10 = lean_array_get_size(x_7);
lean_dec_ref(x_7);
x_11 = lean_nat_dec_lt(x_9, x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_7);
x_14 = lean_box(x_8);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_array_uget_borrowed(x_3, x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = 1;
x_15 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(x_13);
x_16 = 0;
lean_inc(x_12);
x_17 = l_Lean_Compiler_LCNF_mkParam(x_14, x_12, x_15, x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_3, x_2, x_19);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_20, x_2, x_18);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec_ref(x_3);
x_25 = lean_ctor_get(x_17, 0);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
x_26 = x_17;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_91; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 0);
x_91 = !lean_is_exclusive(x_4);
if (x_91 == 0)
{
x_19 = x_4;
x_20 = x_91;
goto block_90;
}
else
{
lean_inc(x_17);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_89; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
x_89 = !lean_is_exclusive(x_17);
if (x_89 == 0)
{
x_23 = x_17;
x_24 = x_89;
goto block_88;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
x_27 = lean_ctor_get(x_18, 2);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
if (x_24 == 0)
{
x_29 = x_23;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_22);
x_29 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_30; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_29);
x_30 = x_19;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_29);
x_30 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; uint8_t x_84; 
lean_inc(x_27);
lean_inc(x_26);
lean_inc_ref(x_25);
x_84 = !lean_is_exclusive(x_18);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_18, 2);
lean_dec(x_85);
x_86 = lean_ctor_get(x_18, 1);
lean_dec(x_86);
x_87 = lean_ctor_get(x_18, 0);
lean_dec(x_87);
x_36 = x_18;
x_37 = x_84;
goto block_83;
}
else
{
lean_dec(x_18);
x_36 = lean_box(0);
x_37 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_array_uget_borrowed(x_1, x_3);
x_39 = lean_ctor_get(x_38, 1);
x_40 = lean_ctor_get(x_38, 2);
x_41 = lean_array_fget(x_25, x_26);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_26, x_42);
lean_dec(x_26);
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_43);
x_44 = x_36;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_25);
lean_ctor_set(x_82, 1, x_43);
lean_ctor_set(x_82, 2, x_27);
x_44 = x_82;
goto block_81;
}
block_81:
{
uint8_t x_45; 
x_45 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(x_40);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_array_push(x_21, x_47);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_48);
x_49 = x_23;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_22);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_49);
lean_ctor_set(x_19, 0, x_44);
x_50 = x_19;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_49);
x_50 = x_52;
goto block_51;
}
block_51:
{
x_10 = x_50;
goto block_14;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_41, 0);
lean_inc(x_55);
lean_dec(x_41);
x_56 = 1;
x_57 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___closed__0));
lean_inc(x_39);
x_58 = l_Lean_Name_str___override(x_39, x_57);
x_59 = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(x_59, 0, x_55);
lean_inc_ref(x_40);
x_60 = l_Lean_Compiler_LCNF_mkLetDecl(x_56, x_58, x_40, x_59, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_61);
x_64 = lean_array_push(x_22, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_66 = lean_array_push(x_21, x_65);
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_64);
lean_ctor_set(x_23, 0, x_66);
x_67 = x_23;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_64);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_67);
lean_ctor_set(x_19, 0, x_44);
x_68 = x_19;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_44);
lean_ctor_set(x_70, 1, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
x_10 = x_68;
goto block_14;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_dec_ref(x_44);
lean_del_object(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_del_object(x_19);
x_73 = lean_ctor_get(x_60, 0);
x_80 = !lean_is_exclusive(x_60);
if (x_80 == 0)
{
x_74 = x_60;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_60);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
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
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_128; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_128 = !lean_is_exclusive(x_1);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_1, 1);
lean_dec(x_129);
x_10 = x_1;
x_11 = x_128;
goto block_127;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = x_128;
goto block_127;
}
block_127:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_array_size(x_9);
x_13 = 0;
lean_inc_ref(x_9);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__0(x_12, x_13, x_9, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_47 = lean_unsigned_to_nat(0u);
x_48 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0));
x_49 = lean_array_get_size(x_9);
x_50 = lean_mk_empty_array_with_capacity(x_49);
x_51 = lean_array_get_size(x_15);
lean_inc(x_15);
x_52 = l_Array_toSubarray___redArg(x_15, x_47, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion_spec__1(x_9, x_12, x_13, x_54, x_2, x_3, x_4, x_5);
lean_dec_ref(x_9);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_109; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_ctor_get(x_56, 1);
x_109 = !lean_is_exclusive(x_56);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_56, 0);
lean_dec(x_110);
x_58 = x_56;
x_59 = x_109;
goto block_108;
}
else
{
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_box(0);
x_59 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_107; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_ctor_get(x_57, 1);
x_107 = !lean_is_exclusive(x_57);
if (x_107 == 0)
{
x_62 = x_57;
x_63 = x_107;
goto block_106;
}
else
{
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_57);
x_62 = lean_box(0);
x_63 = x_107;
goto block_106;
}
block_106:
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_64 = 1;
x_65 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__2));
lean_inc(x_7);
if (x_63 == 0)
{
lean_ctor_set_tag(x_62, 9);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_62, 0, x_7);
x_66 = x_62;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_105, 0, x_7);
lean_ctor_set(x_105, 1, x_60);
x_66 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_67; 
lean_inc_ref(x_8);
x_67 = l_Lean_Compiler_LCNF_mkLetDecl(x_64, x_65, x_8, x_66, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
lean_inc(x_68);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_array_push(x_61, x_69);
x_71 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(x_8);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_del_object(x_58);
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lean_Compiler_LCNF_attachCodeDecls(x_64, x_70, x_73);
lean_dec_ref(x_70);
x_16 = x_74;
x_17 = x_5;
goto block_46;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
lean_dec(x_68);
x_76 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__4));
x_77 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(x_8);
lean_inc_ref(x_8);
if (x_59 == 0)
{
lean_ctor_set_tag(x_58, 13);
lean_ctor_set(x_58, 1, x_75);
lean_ctor_set(x_58, 0, x_8);
x_78 = x_58;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_95, 0, x_8);
lean_ctor_set(x_95, 1, x_75);
x_78 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_79; 
x_79 = l_Lean_Compiler_LCNF_mkLetDecl(x_64, x_76, x_77, x_78, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_80);
x_83 = lean_array_push(x_70, x_82);
x_84 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_84, 0, x_81);
x_85 = l_Lean_Compiler_LCNF_attachCodeDecls(x_64, x_83, x_84);
lean_dec_ref(x_83);
x_16 = x_85;
x_17 = x_5;
goto block_46;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_93; 
lean_dec_ref(x_70);
lean_dec(x_15);
lean_del_object(x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
x_86 = lean_ctor_get(x_79, 0);
x_93 = !lean_is_exclusive(x_79);
if (x_93 == 0)
{
x_87 = x_79;
x_88 = x_93;
goto block_92;
}
else
{
lean_inc(x_86);
lean_dec(x_79);
x_87 = lean_box(0);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
if (x_88 == 0)
{
x_89 = x_87;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_86);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_103; 
lean_dec(x_61);
lean_del_object(x_58);
lean_dec(x_15);
lean_del_object(x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
x_96 = lean_ctor_get(x_67, 0);
x_103 = !lean_is_exclusive(x_67);
if (x_103 == 0)
{
x_97 = x_67;
x_98 = x_103;
goto block_102;
}
else
{
lean_inc(x_96);
lean_dec(x_67);
x_97 = lean_box(0);
x_98 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_99; 
if (x_98 == 0)
{
x_99 = x_97;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_96);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
}
}
}
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
lean_dec(x_15);
lean_del_object(x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
x_111 = lean_ctor_get(x_55, 0);
x_118 = !lean_is_exclusive(x_55);
if (x_118 == 0)
{
x_112 = x_55;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_55);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
block_46:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = l_Lean_Compiler_LCNF_mkBoxedName(x_7);
x_19 = lean_box(0);
x_20 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(x_8);
lean_dec_ref(x_8);
x_21 = 1;
if (x_11 == 0)
{
lean_ctor_set(x_10, 3, x_15);
lean_ctor_set(x_10, 2, x_20);
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_18);
x_22 = x_10;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_19);
lean_ctor_set(x_45, 2, x_20);
lean_ctor_set(x_45, 3, x_15);
x_22 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_16);
x_24 = 0;
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_24);
lean_inc_ref(x_26);
x_27 = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(x_26, x_17);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_27, 0);
lean_dec(x_35);
x_28 = x_27;
x_29 = x_34;
goto block_33;
}
else
{
lean_dec(x_27);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_26);
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_26);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
lean_dec_ref(x_26);
x_36 = lean_ctor_get(x_27, 0);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
x_37 = x_27;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_126; 
lean_del_object(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_119 = lean_ctor_get(x_14, 0);
x_126 = !lean_is_exclusive(x_14);
if (x_126 == 0)
{
x_120 = x_14;
x_121 = x_126;
goto block_125;
}
else
{
lean_inc(x_119);
lean_dec(x_14);
x_120 = lean_box(0);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_121 == 0)
{
x_122 = x_120;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_119);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_2, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_uget_borrowed(x_1, x_2);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
x_18 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(x_17, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
x_10 = x_4;
goto block_14;
}
else
{
lean_object* x_21; 
lean_inc_ref(x_17);
x_21 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion(x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_array_push(x_4, x_22);
x_10 = x_23;
goto block_14;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec_ref(x_4);
x_24 = lean_ctor_get(x_21, 0);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
x_25 = x_21;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec_ref(x_4);
x_32 = lean_ctor_get(x_18, 0);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
x_33 = x_18;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_4);
return x_40;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = ((lean_object*)(l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0));
x_10 = lean_nat_dec_lt(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_le(x_3, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_2, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_2);
x_17 = lean_usize_of_nat(x_12);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(x_1, x_16, x_17, x_9, x_4, x_5, x_6, x_7);
return x_18;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_usize_of_nat(x_2);
x_20 = lean_usize_of_nat(x_3);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0_spec__0(x_1, x_19, x_20, x_9, x_4, x_5, x_6, x_7);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addBoxedVersions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_1);
x_9 = l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0(x_1, x_7, x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_18; 
x_10 = lean_ctor_get(x_9, 0);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
x_11 = x_9;
x_12 = x_18;
goto block_17;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Array_append___redArg(x_1, x_10);
lean_dec(x_10);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_13);
x_14 = x_11;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_dec_ref(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addBoxedVersions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_addBoxedVersions(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___redArg(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_getResultType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_7; uint8_t x_9; uint8_t x_10; 
x_9 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(x_1);
x_10 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(x_2);
if (x_9 == 0)
{
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 1;
x_3 = x_11;
goto block_6;
}
else
{
x_7 = x_9;
goto block_8;
}
}
else
{
x_7 = x_10;
goto block_8;
}
block_6:
{
uint8_t x_4; 
x_4 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
uint8_t x_5; 
x_5 = lean_expr_eqv(x_1, x_2);
return x_5;
}
}
block_8:
{
if (x_7 == 0)
{
return x_7;
}
else
{
x_3 = x_7;
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get(x_45, 1);
x_49 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__0));
x_50 = lean_string_dec_eq(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___closed__1));
x_52 = lean_string_dec_eq(x_48, x_51);
if (x_52 == 0)
{
x_5 = x_3;
goto block_41;
}
else
{
if (lean_obj_tag(x_47) == 0)
{
goto block_44;
}
else
{
x_5 = x_3;
goto block_41;
}
}
}
else
{
if (lean_obj_tag(x_47) == 0)
{
goto block_44;
}
else
{
x_5 = x_3;
goto block_41;
}
}
}
else
{
x_5 = x_3;
goto block_41;
}
}
else
{
x_5 = x_3;
goto block_41;
}
}
else
{
x_5 = x_3;
goto block_41;
}
block_41:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 1;
x_7 = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(x_6, x_1, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_dec_ref(x_9);
return x_7;
}
case 9:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_array_get_size(x_10);
lean_dec_ref(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_21; 
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_7, 0);
lean_dec(x_22);
x_14 = x_7;
x_15 = x_21;
goto block_20;
}
else
{
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
return x_7;
}
}
default: 
{
lean_object* x_23; uint8_t x_24; uint8_t x_30; 
lean_dec(x_9);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_7, 0);
lean_dec(x_31);
x_23 = x_7;
x_24 = x_30;
goto block_29;
}
else
{
lean_dec(x_7);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_25);
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
else
{
lean_object* x_32; uint8_t x_33; uint8_t x_39; 
lean_dec(x_8);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_7, 0);
lean_dec(x_40);
x_32 = x_7;
x_33 = x_39;
goto block_38;
}
else
{
lean_dec(x_7);
x_32 = lean_box(0);
x_33 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_34);
x_35 = x_32;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
return x_7;
}
}
block_44:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(x_1, x_2, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_isExpensiveConstantValueBoxing___redArg(x_1, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_144; 
x_13 = lean_ctor_get(x_12, 0);
x_144 = !lean_is_exclusive(x_12);
if (x_144 == 0)
{
x_14 = x_12;
x_15 = x_144;
goto block_143;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_144;
goto block_143;
}
block_143:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_16 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_1);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_142; 
lean_del_object(x_14);
lean_dec(x_1);
x_20 = lean_ctor_get(x_13, 0);
x_142 = !lean_is_exclusive(x_13);
if (x_142 == 0)
{
x_21 = x_13;
x_22 = x_142;
goto block_141;
}
else
{
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = x_142;
goto block_141;
}
block_141:
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 1;
x_24 = lean_box(0);
lean_inc_ref(x_2);
x_25 = l_Lean_Compiler_LCNF_mkLetDecl(x_23, x_24, x_2, x_20, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
lean_inc_ref(x_3);
x_29 = l_Lean_Compiler_LCNF_mkLetDecl(x_23, x_24, x_3, x_28, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_123; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_ctor_get(x_30, 0);
x_32 = lean_st_ref_get(x_5);
x_33 = lean_ctor_get(x_4, 0);
x_123 = !lean_is_exclusive(x_4);
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_4, 1);
lean_dec(x_124);
x_34 = x_4;
x_35 = x_123;
goto block_122;
}
else
{
lean_inc(x_33);
lean_dec(x_4);
x_34 = lean_box(0);
x_35 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_120; 
x_36 = lean_ctor_get(x_32, 1);
x_120 = !lean_is_exclusive(x_32);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_32, 0);
lean_dec(x_121);
x_37 = x_32;
x_38 = x_120;
goto block_119;
}
else
{
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_39; 
lean_inc(x_31);
if (x_22 == 0)
{
lean_ctor_set_tag(x_21, 5);
lean_ctor_set(x_21, 0, x_31);
x_39 = x_21;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_118, 0, x_31);
x_39 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_40; 
if (x_38 == 0)
{
lean_ctor_set(x_37, 1, x_39);
lean_ctor_set(x_37, 0, x_30);
x_40 = x_37;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_30);
lean_ctor_set(x_116, 1, x_39);
x_40 = x_116;
goto block_115;
}
block_115:
{
uint8_t x_41; lean_object* x_42; 
x_41 = 1;
if (x_35 == 0)
{
lean_ctor_set(x_34, 1, x_40);
lean_ctor_set(x_34, 0, x_26);
x_42 = x_34;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_26);
lean_ctor_set(x_114, 1, x_40);
x_42 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__1));
x_44 = lean_name_append_index_after(x_43, x_36);
x_45 = l_Lean_Name_append(x_33, x_44);
x_46 = lean_box(0);
x_47 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___closed__2));
lean_inc(x_45);
x_48 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_3);
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_41);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_42);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_51);
x_52 = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(x_23, x_51, x_8, x_9);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_85; 
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_54 = lean_st_ref_take(x_5);
x_55 = lean_ctor_get(x_54, 0);
x_56 = lean_ctor_get(x_54, 1);
x_85 = !lean_is_exclusive(x_54);
if (x_85 == 0)
{
x_57 = x_54;
x_58 = x_85;
goto block_84;
}
else
{
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_54);
x_57 = lean_box(0);
x_58 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_inc_ref(x_51);
x_59 = lean_array_push(x_55, x_51);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_56, x_60);
lean_dec(x_56);
if (x_58 == 0)
{
lean_ctor_set(x_57, 1, x_61);
lean_ctor_set(x_57, 0, x_59);
x_62 = x_57;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_59);
lean_ctor_set(x_83, 1, x_61);
x_62 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_st_ref_set(x_5, x_62);
x_64 = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(x_51, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; uint8_t x_72; 
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_64, 0);
lean_dec(x_73);
x_65 = x_64;
x_66 = x_72;
goto block_71;
}
else
{
lean_dec(x_64);
x_65 = lean_box(0);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_67, 0, x_45);
lean_ctor_set(x_67, 1, x_47);
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_67);
x_68 = x_65;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec(x_45);
x_74 = lean_ctor_get(x_64, 0);
x_81 = !lean_is_exclusive(x_64);
if (x_81 == 0)
{
x_75 = x_64;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_64);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_45);
x_86 = lean_ctor_get(x_53, 0);
lean_inc(x_86);
lean_dec_ref(x_53);
x_87 = l_Lean_Compiler_LCNF_eraseDecl(x_23, x_51, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; uint8_t x_95; 
x_95 = !lean_is_exclusive(x_87);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_87, 0);
lean_dec(x_96);
x_88 = x_87;
x_89 = x_95;
goto block_94;
}
else
{
lean_dec(x_87);
x_88 = lean_box(0);
x_89 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_47);
if (x_89 == 0)
{
lean_ctor_set(x_88, 0, x_90);
x_91 = x_88;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_90);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_104; 
lean_dec(x_86);
x_97 = lean_ctor_get(x_87, 0);
x_104 = !lean_is_exclusive(x_87);
if (x_104 == 0)
{
x_98 = x_87;
x_99 = x_104;
goto block_103;
}
else
{
lean_inc(x_97);
lean_dec(x_87);
x_98 = lean_box(0);
x_99 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_100; 
if (x_99 == 0)
{
x_100 = x_98;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_97);
x_100 = x_102;
goto block_101;
}
block_101:
{
return x_100;
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_112; 
lean_dec_ref(x_51);
lean_dec(x_45);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_105 = lean_ctor_get(x_52, 0);
x_112 = !lean_is_exclusive(x_52);
if (x_112 == 0)
{
x_106 = x_52;
x_107 = x_112;
goto block_111;
}
else
{
lean_inc(x_105);
lean_dec(x_52);
x_106 = lean_box(0);
x_107 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_108; 
if (x_107 == 0)
{
x_108 = x_106;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_105);
x_108 = x_110;
goto block_109;
}
block_109:
{
return x_108;
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
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_132; 
lean_dec(x_26);
lean_del_object(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_125 = lean_ctor_get(x_29, 0);
x_132 = !lean_is_exclusive(x_29);
if (x_132 == 0)
{
x_126 = x_29;
x_127 = x_132;
goto block_131;
}
else
{
lean_inc(x_125);
lean_dec(x_29);
x_126 = lean_box(0);
x_127 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_128; 
if (x_127 == 0)
{
x_128 = x_126;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_125);
x_128 = x_130;
goto block_129;
}
block_129:
{
return x_128;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_140; 
lean_del_object(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_133 = lean_ctor_get(x_25, 0);
x_140 = !lean_is_exclusive(x_25);
if (x_140 == 0)
{
x_134 = x_25;
x_135 = x_140;
goto block_139;
}
else
{
lean_inc(x_133);
lean_dec(x_25);
x_134 = lean_box(0);
x_135 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_136; 
if (x_135 == 0)
{
x_136 = x_134;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_133);
x_136 = x_138;
goto block_137;
}
block_137:
{
return x_136;
}
}
}
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_152; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_145 = lean_ctor_get(x_12, 0);
x_152 = !lean_is_exclusive(x_12);
if (x_152 == 0)
{
x_146 = x_12;
x_147 = x_152;
goto block_151;
}
else
{
lean_inc(x_145);
lean_dec(x_12);
x_146 = lean_box(0);
x_147 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_148; 
if (x_147 == 0)
{
x_148 = x_146;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_145);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_153 = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(x_153, 0, x_1);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_getType(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(x_12, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
x_14 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(x_1, x_12, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = 1;
x_17 = lean_box(0);
x_18 = l_Lean_Compiler_LCNF_mkLetDecl(x_16, x_17, x_2, x_15, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_apply_8(x_3, x_20, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
x_22 = lean_ctor_get(x_21, 0);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
x_23 = x_21;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_22);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_25);
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
lean_dec(x_19);
return x_21;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_31 = lean_ctor_get(x_18, 0);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
x_32 = x_18;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_39 = lean_ctor_get(x_14, 0);
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
x_40 = x_14;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_14);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_12);
lean_dec_ref(x_2);
x_47 = lean_apply_8(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_11, 0);
x_55 = !lean_is_exclusive(x_11);
if (x_55 == 0)
{
x_49 = x_11;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_11);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castVarIfNeeded(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(x_1, x_3);
x_12 = lean_apply_8(x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_2);
x_11 = lean_apply_8(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l_Lean_Compiler_LCNF_getType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(x_14, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
lean_inc(x_12);
x_16 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(x_12, x_14, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = 1;
x_19 = lean_box(0);
x_20 = l_Lean_Compiler_LCNF_mkLetDecl(x_18, x_19, x_2, x_17, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(x_1, x_3, x_22, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_32; 
x_24 = lean_ctor_get(x_23, 0);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
x_25 = x_23;
x_26 = x_32;
goto block_31;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_24);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_27);
x_28 = x_25;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
else
{
lean_dec(x_21);
return x_23;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec_ref(x_1);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_33 = lean_ctor_get(x_20, 0);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
x_34 = x_20;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec_ref(x_1);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_41 = lean_ctor_get(x_16, 0);
x_48 = !lean_is_exclusive(x_16);
if (x_48 == 0)
{
x_42 = x_16;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_16);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_49; 
lean_inc(x_12);
lean_dec(x_14);
lean_dec_ref(x_2);
x_49 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___lam__0(x_1, x_3, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec_ref(x_1);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_50 = lean_ctor_get(x_13, 0);
x_57 = !lean_is_exclusive(x_13);
if (x_57 == 0)
{
x_51 = x_13;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_13);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgIfNeeded(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_4, x_1);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_84; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
x_84 = !lean_is_exclusive(x_5);
if (x_84 == 0)
{
x_22 = x_5;
x_23 = x_84;
goto block_83;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_box(0);
x_23 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_24; 
x_24 = lean_array_fget(x_2, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_push(x_21, x_24);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_25);
x_26 = x_22;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
x_13 = x_26;
goto block_17;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = l_Lean_Compiler_LCNF_getType(x_29, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
lean_inc_ref(x_3);
lean_inc(x_4);
x_32 = lean_apply_1(x_3, x_4);
x_33 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; uint8_t x_69; 
lean_inc(x_29);
x_69 = !lean_is_exclusive(x_24);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_24, 0);
lean_dec(x_70);
x_34 = x_24;
x_35 = x_69;
goto block_68;
}
else
{
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_36; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_32);
x_36 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(x_29, x_31, x_32, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = 1;
x_39 = lean_box(0);
x_40 = l_Lean_Compiler_LCNF_mkLetDecl(x_38, x_39, x_32, x_37, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_42);
x_43 = x_34;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_42);
x_43 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_array_push(x_21, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_41);
x_46 = lean_array_push(x_20, x_45);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_44);
lean_ctor_set(x_22, 0, x_46);
x_47 = x_22;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
x_13 = x_47;
goto block_17;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_del_object(x_34);
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_52 = lean_ctor_get(x_40, 0);
x_59 = !lean_is_exclusive(x_40);
if (x_59 == 0)
{
x_53 = x_40;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_40);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_67; 
lean_del_object(x_34);
lean_dec_ref(x_32);
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_60 = lean_ctor_get(x_36, 0);
x_67 = !lean_is_exclusive(x_36);
if (x_67 == 0)
{
x_61 = x_36;
x_62 = x_67;
goto block_66;
}
else
{
lean_inc(x_60);
lean_dec(x_36);
x_61 = lean_box(0);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_62 == 0)
{
x_63 = x_61;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_60);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_32);
lean_dec(x_31);
x_71 = lean_array_push(x_21, x_24);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_71);
x_72 = x_22;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_20);
lean_ctor_set(x_74, 1, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
x_13 = x_72;
goto block_17;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_dec_ref(x_24);
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_75 = lean_ctor_get(x_30, 0);
x_82 = !lean_is_exclusive(x_30);
if (x_82 == 0)
{
x_76 = x_30;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_30);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkBoxedVersion___closed__0));
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(x_10, x_1, x_2, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_32; 
x_16 = lean_ctor_get(x_15, 0);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
x_17 = x_15;
x_18 = x_32;
goto block_31;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_30; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
x_21 = x_16;
x_22 = x_30;
goto block_29;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_23; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_20);
x_23 = x_21;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_19);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_23);
x_24 = x_17;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
x_33 = lean_ctor_get(x_15, 0);
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
x_34 = x_15;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = l_Lean_Compiler_LCNF_instInhabitedParam_default(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___closed__0);
x_4 = lean_array_get_borrowed(x_3, x_1, x_2);
x_5 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___lam__0___boxed), 2, 1);
lean_closure_set(x_11, 0, x_2);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
x_12 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_apply_8(x_3, x_14, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_26; 
x_17 = lean_ctor_get(x_16, 0);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
x_18 = x_16;
x_19 = x_26;
goto block_25;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_26;
goto block_25;
}
block_25:
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = 1;
x_21 = l_Lean_Compiler_LCNF_attachCodeDecls(x_20, x_15, x_17);
lean_dec(x_15);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_21);
x_22 = x_18;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
else
{
lean_dec(x_15);
return x_16;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_27 = lean_ctor_get(x_12, 0);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
x_28 = x_12;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_12);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeeded(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___closed__0));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
x_11 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_8(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_25; 
x_16 = lean_ctor_get(x_15, 0);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
x_17 = x_15;
x_18 = x_25;
goto block_24;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_25;
goto block_24;
}
block_24:
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 1;
x_20 = l_Lean_Compiler_LCNF_attachCodeDecls(x_19, x_14, x_16);
lean_dec(x_14);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_20);
x_21 = x_17;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
else
{
lean_dec(x_14);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_26 = lean_ctor_get(x_11, 0);
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
x_27 = x_11;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_11);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(611u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 2);
x_15 = lean_ctor_get(x_2, 3);
x_16 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(x_14);
if (x_16 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ptr_addr(x_18);
x_20 = lean_ptr_addr(x_3);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
x_9 = x_21;
goto block_13;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = lean_ptr_addr(x_17);
x_23 = lean_ptr_addr(x_2);
x_24 = lean_usize_dec_eq(x_22, x_23);
x_9 = x_24;
goto block_13;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_25 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
x_26 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_1);
x_28 = 1;
x_29 = lean_box(0);
x_30 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
lean_inc(x_15);
x_31 = l_Lean_Compiler_LCNF_mkLetDecl(x_28, x_29, x_30, x_15, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_alloc_ctor(14, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_28, x_2, x_34, x_5);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_45; 
x_36 = lean_ctor_get(x_35, 0);
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
x_37 = x_35;
x_38 = x_45;
goto block_44;
}
else
{
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_3);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_39);
if (x_38 == 0)
{
lean_ctor_set(x_37, 0, x_40);
x_41 = x_37;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_dec(x_32);
lean_dec_ref(x_3);
x_46 = lean_ctor_get(x_35, 0);
x_53 = !lean_is_exclusive(x_35);
if (x_53 == 0)
{
x_47 = x_35;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_35);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_54 = lean_ctor_get(x_31, 0);
x_61 = !lean_is_exclusive(x_31);
if (x_61 == 0)
{
x_55 = x_31;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_31);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
block_13:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(x_1, x_2, x_3, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_2, 3);
x_19 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(x_17, x_3);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_1);
x_20 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(x_17);
x_21 = 1;
x_22 = lean_box(0);
lean_inc(x_18);
x_23 = l_Lean_Compiler_LCNF_mkLetDecl(x_21, x_22, x_20, x_18, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_8);
lean_inc_ref(x_17);
lean_inc_ref(x_26);
lean_inc(x_25);
x_27 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(x_25, x_26, x_17, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_21, x_2, x_28, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_39; 
x_30 = lean_ctor_get(x_29, 0);
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
x_31 = x_29;
x_32 = x_39;
goto block_38;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_4);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_33);
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_34);
x_35 = x_31;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_24);
lean_dec_ref(x_4);
x_40 = lean_ctor_get(x_29, 0);
x_47 = !lean_is_exclusive(x_29);
if (x_47 == 0)
{
x_41 = x_29;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_48 = lean_ctor_get(x_27, 0);
x_55 = !lean_is_exclusive(x_27);
if (x_55 == 0)
{
x_49 = x_27;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_27);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_56 = lean_ctor_get(x_23, 0);
x_63 = !lean_is_exclusive(x_23);
if (x_63 == 0)
{
x_57 = x_23;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_23);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_1, 0);
x_65 = lean_ctor_get(x_1, 1);
x_66 = lean_ptr_addr(x_65);
x_67 = lean_ptr_addr(x_4);
x_68 = lean_usize_dec_eq(x_66, x_67);
if (x_68 == 0)
{
x_12 = x_68;
goto block_16;
}
else
{
size_t x_69; size_t x_70; uint8_t x_71; 
x_69 = lean_ptr_addr(x_64);
x_70 = lean_ptr_addr(x_2);
x_71 = lean_usize_dec_eq(x_69, x_70);
x_12 = x_71;
goto block_16;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_72 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
x_73 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(x_72);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
block_16:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_4);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_3);
return x_12;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_74; 
x_9 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = lean_ctor_get(x_10, 0);
x_74 = !lean_is_exclusive(x_10);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_10, 1);
lean_dec(x_75);
x_12 = x_10;
x_13 = x_74;
goto block_73;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_71; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_71 = !lean_is_exclusive(x_11);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_11, 1);
lean_dec(x_72);
x_18 = x_11;
x_19 = x_71;
goto block_70;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1));
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2));
lean_inc_ref(x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_17);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_16);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_15);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_25);
lean_ctor_set(x_18, 3, x_26);
lean_ctor_set(x_18, 2, x_27);
lean_ctor_set(x_18, 1, x_20);
lean_ctor_set(x_18, 0, x_24);
x_28 = x_18;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_69, 0, x_24);
lean_ctor_set(x_69, 1, x_20);
lean_ctor_set(x_69, 2, x_27);
lean_ctor_set(x_69, 3, x_26);
lean_ctor_set(x_69, 4, x_25);
x_28 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_29; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_28);
x_29 = x_12;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_28);
lean_ctor_set(x_67, 1, x_21);
x_29 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_64; 
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = lean_ctor_get(x_30, 0);
x_64 = !lean_is_exclusive(x_30);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_30, 1);
lean_dec(x_65);
x_32 = x_30;
x_33 = x_64;
goto block_63;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_61; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_61 = !lean_is_exclusive(x_31);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_31, 1);
lean_dec(x_62);
x_38 = x_31;
x_39 = x_61;
goto block_60;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3));
x_41 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4));
lean_inc_ref(x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_37);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_36);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_47, 0, x_35);
if (x_39 == 0)
{
lean_ctor_set(x_38, 4, x_45);
lean_ctor_set(x_38, 3, x_46);
lean_ctor_set(x_38, 2, x_47);
lean_ctor_set(x_38, 1, x_40);
lean_ctor_set(x_38, 0, x_44);
x_48 = x_38;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_40);
lean_ctor_set(x_59, 2, x_47);
lean_ctor_set(x_59, 3, x_46);
lean_ctor_set(x_59, 4, x_45);
x_48 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_49; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 1, x_41);
lean_ctor_set(x_32, 0, x_48);
x_49 = x_32;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_41);
x_49 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = l_Lean_instInhabitedExpr;
x_52 = l_instInhabitedOfMonad___redArg(x_50, x_51);
x_53 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = lean_panic_fn(x_53, x_1);
x_55 = lean_apply_7(x_54, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_55;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__4));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__7));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_unsigned_to_nat(301u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
x_2 = lean_unsigned_to_nat(44u);
x_3 = lean_unsigned_to_nat(316u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__10));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_40; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_10 = lean_ctor_get(x_2, 0);
x_40 = !lean_is_exclusive(x_2);
if (x_40 == 0)
{
x_11 = x_2;
x_12 = x_40;
goto block_39;
}
else
{
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = x_40;
goto block_39;
}
block_39:
{
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_26; 
lean_del_object(x_11);
x_13 = lean_ctor_get(x_10, 0);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
x_14 = x_10;
x_15 = x_26;
goto block_25;
}
else
{
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_maxSmallNat;
x_17 = lean_nat_dec_le(x_13, x_16);
lean_dec(x_13);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_1);
x_18 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_1);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_1);
x_21 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_21);
x_22 = x_14;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
case 1:
{
lean_object* x_27; uint8_t x_28; uint8_t x_34; 
lean_del_object(x_11);
lean_dec_ref(x_1);
x_34 = !lean_is_exclusive(x_10);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_10, 0);
lean_dec(x_35);
x_27 = x_10;
x_28 = x_34;
goto block_33;
}
else
{
lean_dec(x_10);
x_27 = lean_box(0);
x_28 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
if (x_28 == 0)
{
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_29);
x_30 = x_27;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
default: 
{
lean_object* x_36; 
lean_dec_ref(x_10);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_1);
x_36 = x_11;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_1);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
case 1:
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_41 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__2);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
case 5:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_43);
lean_dec_ref(x_2);
x_44 = l_Lean_Compiler_LCNF_CtorInfo_type(x_43);
lean_dec_ref(x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
case 7:
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_2);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_46 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
case 9:
{
lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
lean_dec_ref(x_2);
x_49 = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(x_48, x_8);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_61; 
x_50 = lean_ctor_get(x_49, 0);
x_61 = !lean_is_exclusive(x_49);
if (x_61 == 0)
{
x_51 = x_49;
x_52 = x_61;
goto block_60;
}
else
{
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_box(0);
x_52 = x_61;
goto block_60;
}
block_60:
{
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec_ref(x_50);
x_54 = lean_ctor_get(x_53, 2);
lean_inc_ref(x_54);
lean_dec(x_53);
if (x_52 == 0)
{
lean_ctor_set(x_51, 0, x_54);
x_55 = x_51;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_54);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_del_object(x_51);
lean_dec(x_50);
x_58 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__11);
x_59 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(x_58, x_3, x_4, x_5, x_6, x_7, x_8);
return x_59;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_62 = lean_ctor_get(x_49, 0);
x_69 = !lean_is_exclusive(x_49);
if (x_69 == 0)
{
x_63 = x_49;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_49);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
case 10:
{
lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_2);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_70 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__5);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
case 13:
{
lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_72 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12);
x_73 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(x_72, x_3, x_4, x_5, x_6, x_7, x_8);
return x_73;
}
case 14:
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_74 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12);
x_75 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(x_74, x_3, x_4, x_5, x_6, x_7, x_8);
return x_75;
}
case 15:
{
lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_76 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__12);
x_77 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0(x_76, x_3, x_4, x_5, x_6, x_7, x_8);
return x_77;
}
default: 
{
lean_object* x_78; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_1);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_74; 
x_9 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__0);
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = lean_ctor_get(x_10, 0);
x_74 = !lean_is_exclusive(x_10);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_10, 1);
lean_dec(x_75);
x_12 = x_10;
x_13 = x_74;
goto block_73;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_71; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_71 = !lean_is_exclusive(x_11);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_11, 1);
lean_dec(x_72);
x_18 = x_11;
x_19 = x_71;
goto block_70;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__1));
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__2));
lean_inc_ref(x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_17);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_16);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_15);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_25);
lean_ctor_set(x_18, 3, x_26);
lean_ctor_set(x_18, 2, x_27);
lean_ctor_set(x_18, 1, x_20);
lean_ctor_set(x_18, 0, x_24);
x_28 = x_18;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_69, 0, x_24);
lean_ctor_set(x_69, 1, x_20);
lean_ctor_set(x_69, 2, x_27);
lean_ctor_set(x_69, 3, x_26);
lean_ctor_set(x_69, 4, x_25);
x_28 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_29; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_28);
x_29 = x_12;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_28);
lean_ctor_set(x_67, 1, x_21);
x_29 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_64; 
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = lean_ctor_get(x_30, 0);
x_64 = !lean_is_exclusive(x_30);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_30, 1);
lean_dec(x_65);
x_32 = x_30;
x_33 = x_64;
goto block_63;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_61; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_61 = !lean_is_exclusive(x_31);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_31, 1);
lean_dec(x_62);
x_38 = x_31;
x_39 = x_61;
goto block_60;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__3));
x_41 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType_spec__0___closed__4));
lean_inc_ref(x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_37);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_36);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_47, 0, x_35);
if (x_39 == 0)
{
lean_ctor_set(x_38, 4, x_45);
lean_ctor_set(x_38, 3, x_46);
lean_ctor_set(x_38, 2, x_47);
lean_ctor_set(x_38, 1, x_40);
lean_ctor_set(x_38, 0, x_44);
x_48 = x_38;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_40);
lean_ctor_set(x_59, 2, x_47);
lean_ctor_set(x_59, 3, x_46);
lean_ctor_set(x_59, 4, x_45);
x_48 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_49; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 1, x_41);
lean_ctor_set(x_32, 0, x_48);
x_49 = x_32;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_41);
x_49 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0___closed__0);
x_52 = l_instInhabitedOfMonad___redArg(x_50, x_51);
x_53 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = lean_panic_fn(x_53, x_1);
x_55 = lean_apply_7(x_54, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_55;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_boxArgsIfNeeded___lam__0___closed__2);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Compiler_LCNF_instInhabitedParam_default(x_1);
x_5 = lean_array_get_borrowed(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_6);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_instBEqFVarId_beq(x_1, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_2);
x_12 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_12, 0, x_3);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_20; size_t x_24; size_t x_25; uint8_t x_26; 
x_15 = lean_ctor_get(x_8, 1);
x_24 = lean_ptr_addr(x_5);
x_25 = lean_ptr_addr(x_2);
x_26 = lean_usize_dec_eq(x_24, x_25);
if (x_26 == 0)
{
x_20 = x_26;
goto block_23;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = lean_ptr_addr(x_6);
x_28 = lean_ptr_addr(x_15);
x_29 = lean_usize_dec_eq(x_27, x_28);
x_20 = x_29;
goto block_23;
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_15);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_7);
lean_ctor_set(x_16, 3, x_2);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
block_23:
{
if (x_20 == 0)
{
lean_dec_ref(x_4);
goto block_19;
}
else
{
uint8_t x_21; 
x_21 = l_Lean_instBEqFVarId_beq(x_3, x_7);
if (x_21 == 0)
{
lean_dec_ref(x_4);
goto block_19;
}
else
{
lean_object* x_22; 
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_4);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_30);
x_10 = x_30;
goto block_29;
}
case 1:
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_31);
x_10 = x_31;
goto block_29;
}
default: 
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_32);
x_10 = x_32;
goto block_29;
}
}
block_29:
{
lean_object* x_11; 
x_11 = lean_apply_8(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_11, 0);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_13 = x_11;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_1, x_12);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_11, 0);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
x_22 = x_11;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; size_t x_39; uint8_t x_40; 
x_39 = lean_ptr_addr(x_1);
x_40 = lean_usize_dec_eq(x_39, x_39);
if (x_40 == 0)
{
x_17 = x_40;
goto block_38;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_eq(x_2, x_2);
x_17 = x_41;
goto block_38;
}
block_38:
{
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_8);
x_18 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_3);
lean_ctor_set(x_18, 3, x_9);
lean_ctor_set(x_18, 4, x_4);
lean_ctor_set(x_18, 5, x_5);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_eq(x_3, x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_8);
x_21 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_3);
lean_ctor_set(x_21, 3, x_9);
lean_ctor_set(x_21, 4, x_4);
lean_ctor_set(x_21, 5, x_5);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_ptr_addr(x_6);
x_24 = lean_ptr_addr(x_9);
x_25 = lean_usize_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_8);
x_26 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_3);
lean_ctor_set(x_26, 3, x_9);
lean_ctor_set(x_26, 4, x_4);
lean_ctor_set(x_26, 5, x_5);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
size_t x_28; uint8_t x_29; 
x_28 = lean_ptr_addr(x_4);
x_29 = lean_usize_dec_eq(x_28, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_8);
x_30 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_9);
lean_ctor_set(x_30, 4, x_4);
lean_ctor_set(x_30, 5, x_5);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
size_t x_32; size_t x_33; uint8_t x_34; 
x_32 = lean_ptr_addr(x_7);
x_33 = lean_ptr_addr(x_5);
x_34 = lean_usize_dec_eq(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_8);
x_35 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set(x_35, 2, x_3);
lean_ctor_set(x_35, 3, x_9);
lean_ctor_set(x_35, 4, x_4);
lean_ctor_set(x_35, 5, x_5);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_8);
return x_37;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; size_t x_30; uint8_t x_31; 
x_30 = lean_ptr_addr(x_1);
x_31 = lean_usize_dec_eq(x_30, x_30);
if (x_31 == 0)
{
x_15 = x_31;
goto block_29;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_eq(x_2, x_2);
x_15 = x_32;
goto block_29;
}
block_29:
{
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_6);
x_16 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_7);
lean_ctor_set(x_16, 3, x_3);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = lean_ptr_addr(x_4);
x_19 = lean_ptr_addr(x_7);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_6);
x_21 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_7);
lean_ctor_set(x_21, 3, x_3);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_ptr_addr(x_5);
x_24 = lean_ptr_addr(x_3);
x_25 = lean_usize_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_6);
x_26 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_7);
lean_ctor_set(x_26, 3, x_3);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_6);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Compiler_LCNF_instInhabitedParam_default(x_1);
x_5 = lean_array_get_borrowed(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_6);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_unsigned_to_nat(336u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_unsigned_to_nat(341u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
x_2 = lean_unsigned_to_nat(44u);
x_3 = lean_unsigned_to_nat(353u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_12);
lean_inc_ref(x_11);
x_13 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType(x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_389; 
x_14 = lean_ctor_get(x_13, 0);
x_389 = !lean_is_exclusive(x_13);
if (x_389 == 0)
{
x_15 = x_13;
x_16 = x_389;
goto block_388;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_389;
goto block_388;
}
block_388:
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_25; lean_object* x_26; lean_object* x_30; 
x_17 = 1;
lean_inc(x_14);
x_30 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(x_17, x_2, x_14, x_12, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_379; 
x_31 = lean_ctor_get(x_30, 0);
x_379 = !lean_is_exclusive(x_30);
if (x_379 == 0)
{
x_32 = x_30;
x_33 = x_379;
goto block_378;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_379;
goto block_378;
}
block_378:
{
lean_object* x_34; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_34 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_377; 
x_35 = lean_ctor_get(x_34, 0);
x_377 = !lean_is_exclusive(x_34);
if (x_377 == 0)
{
x_36 = x_34;
x_37 = x_377;
goto block_376;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_377;
goto block_376;
}
block_376:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_43; uint8_t x_44; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_58; 
x_58 = lean_ctor_get(x_31, 3);
switch (lean_obj_tag(x_58)) {
case 4:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_del_object(x_36);
lean_del_object(x_32);
lean_del_object(x_15);
lean_dec(x_14);
x_59 = lean_ctor_get(x_58, 1);
x_60 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_61 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(x_59, x_60, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc_ref(x_58);
x_65 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_17, x_58, x_63);
x_66 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_17, x_31, x_65, x_7);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg(x_1, x_67, x_35, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_77; 
x_69 = lean_ctor_get(x_68, 0);
x_77 = !lean_is_exclusive(x_68);
if (x_77 == 0)
{
x_70 = x_68;
x_71 = x_77;
goto block_76;
}
else
{
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
x_71 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_Compiler_LCNF_attachCodeDecls(x_17, x_64, x_69);
lean_dec(x_64);
if (x_71 == 0)
{
lean_ctor_set(x_70, 0, x_72);
x_73 = x_70;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
else
{
lean_dec(x_64);
return x_68;
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_64);
lean_dec(x_35);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_78 = lean_ctor_get(x_66, 0);
x_85 = !lean_is_exclusive(x_66);
if (x_85 == 0)
{
x_79 = x_66;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_66);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_93; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_86 = lean_ctor_get(x_61, 0);
x_93 = !lean_is_exclusive(x_61);
if (x_93 == 0)
{
x_87 = x_61;
x_88 = x_93;
goto block_92;
}
else
{
lean_inc(x_86);
lean_dec(x_61);
x_87 = lean_box(0);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
if (x_88 == 0)
{
x_89 = x_87;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_86);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
case 5:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_163; 
lean_del_object(x_32);
x_94 = lean_ctor_get(x_58, 0);
x_95 = lean_ctor_get(x_58, 1);
x_96 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
x_163 = l_Lean_Compiler_LCNF_CtorInfo_isScalar(x_94);
if (x_163 == 0)
{
x_97 = x_163;
goto block_162;
}
else
{
uint8_t x_164; 
x_164 = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(x_14);
x_97 = x_164;
goto block_162;
}
block_162:
{
if (x_97 == 0)
{
lean_object* x_98; 
lean_del_object(x_36);
lean_dec(x_14);
lean_inc(x_7);
x_98 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(x_95, x_96, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc_ref(x_58);
x_102 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_17, x_58, x_100);
x_103 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_17, x_31, x_102, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_103) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; size_t x_107; size_t x_108; uint8_t x_109; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = lean_ctor_get(x_1, 0);
x_106 = lean_ctor_get(x_1, 1);
x_107 = lean_ptr_addr(x_106);
x_108 = lean_ptr_addr(x_35);
x_109 = lean_usize_dec_eq(x_107, x_108);
if (x_109 == 0)
{
x_53 = x_104;
x_54 = x_101;
x_55 = x_109;
goto block_57;
}
else
{
size_t x_110; size_t x_111; uint8_t x_112; 
x_110 = lean_ptr_addr(x_105);
x_111 = lean_ptr_addr(x_104);
x_112 = lean_usize_dec_eq(x_110, x_111);
x_53 = x_104;
x_54 = x_101;
x_55 = x_112;
goto block_57;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec_ref(x_103);
lean_dec(x_35);
lean_dec_ref(x_1);
x_113 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
x_114 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(x_113);
x_18 = x_101;
x_19 = x_114;
goto block_24;
}
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_122; 
lean_dec(x_101);
lean_dec(x_35);
lean_del_object(x_15);
lean_dec_ref(x_1);
x_115 = lean_ctor_get(x_103, 0);
x_122 = !lean_is_exclusive(x_103);
if (x_122 == 0)
{
x_116 = x_103;
x_117 = x_122;
goto block_121;
}
else
{
lean_inc(x_115);
lean_dec(x_103);
x_116 = lean_box(0);
x_117 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_118; 
if (x_117 == 0)
{
x_118 = x_116;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_115);
x_118 = x_120;
goto block_119;
}
block_119:
{
return x_118;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_130; 
lean_dec(x_35);
lean_dec(x_31);
lean_del_object(x_15);
lean_dec(x_7);
lean_dec_ref(x_1);
x_123 = lean_ctor_get(x_98, 0);
x_130 = !lean_is_exclusive(x_98);
if (x_130 == 0)
{
x_124 = x_98;
x_125 = x_130;
goto block_129;
}
else
{
lean_inc(x_123);
lean_dec(x_98);
x_124 = lean_box(0);
x_125 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_126; 
if (x_125 == 0)
{
x_126 = x_124;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_123);
x_126 = x_128;
goto block_127;
}
block_127:
{
return x_126;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_del_object(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_131 = lean_ctor_get(x_94, 1);
x_132 = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(x_14, x_131);
lean_dec(x_14);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_17, x_31, x_133, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_134) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; size_t x_138; size_t x_139; uint8_t x_140; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = lean_ctor_get(x_1, 0);
x_137 = lean_ctor_get(x_1, 1);
x_138 = lean_ptr_addr(x_137);
x_139 = lean_ptr_addr(x_35);
x_140 = lean_usize_dec_eq(x_138, x_139);
if (x_140 == 0)
{
x_43 = x_135;
x_44 = x_140;
goto block_52;
}
else
{
size_t x_141; size_t x_142; uint8_t x_143; 
x_141 = lean_ptr_addr(x_136);
x_142 = lean_ptr_addr(x_135);
x_143 = lean_usize_dec_eq(x_141, x_142);
x_43 = x_135;
x_44 = x_143;
goto block_52;
}
}
else
{
lean_object* x_144; uint8_t x_145; uint8_t x_152; 
lean_del_object(x_36);
lean_dec(x_35);
lean_dec_ref(x_1);
x_152 = !lean_is_exclusive(x_134);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_134, 0);
lean_dec(x_153);
x_144 = x_134;
x_145 = x_152;
goto block_151;
}
else
{
lean_dec(x_134);
x_144 = lean_box(0);
x_145 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
x_147 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(x_146);
if (x_145 == 0)
{
lean_ctor_set(x_144, 0, x_147);
x_148 = x_144;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_147);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; uint8_t x_161; 
lean_del_object(x_36);
lean_dec(x_35);
lean_dec_ref(x_1);
x_154 = lean_ctor_get(x_134, 0);
x_161 = !lean_is_exclusive(x_134);
if (x_161 == 0)
{
x_155 = x_134;
x_156 = x_161;
goto block_160;
}
else
{
lean_inc(x_154);
lean_dec(x_134);
x_155 = lean_box(0);
x_156 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_157; 
if (x_156 == 0)
{
x_157 = x_155;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_154);
x_157 = x_159;
goto block_158;
}
block_158:
{
return x_157;
}
}
}
}
}
}
case 9:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_del_object(x_36);
lean_del_object(x_32);
lean_del_object(x_15);
lean_dec(x_14);
x_165 = lean_ctor_get(x_58, 0);
x_166 = lean_ctor_get(x_58, 1);
lean_inc(x_165);
x_167 = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(x_165, x_9);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
if (lean_obj_tag(x_168) == 1)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec_ref(x_168);
x_170 = lean_ctor_get(x_169, 2);
lean_inc_ref(x_170);
x_171 = lean_ctor_get(x_169, 3);
lean_inc_ref(x_171);
lean_dec(x_169);
x_172 = lean_box(x_17);
x_173 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___lam__2___boxed), 3, 2);
lean_closure_set(x_173, 0, x_172);
lean_closure_set(x_173, 1, x_171);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
x_174 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(x_166, x_173, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec_ref(x_174);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
lean_inc_ref(x_58);
x_178 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_17, x_58, x_176);
x_179 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_17, x_31, x_178, x_7);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec_ref(x_179);
x_181 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castResultIfNeeded(x_1, x_180, x_170, x_35, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_170);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_190; 
x_182 = lean_ctor_get(x_181, 0);
x_190 = !lean_is_exclusive(x_181);
if (x_190 == 0)
{
x_183 = x_181;
x_184 = x_190;
goto block_189;
}
else
{
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_box(0);
x_184 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_185; lean_object* x_186; 
x_185 = l_Lean_Compiler_LCNF_attachCodeDecls(x_17, x_177, x_182);
lean_dec(x_177);
if (x_184 == 0)
{
lean_ctor_set(x_183, 0, x_185);
x_186 = x_183;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_188, 0, x_185);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
}
else
{
lean_dec(x_177);
return x_181;
}
}
else
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_198; 
lean_dec(x_177);
lean_dec_ref(x_170);
lean_dec(x_35);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_191 = lean_ctor_get(x_179, 0);
x_198 = !lean_is_exclusive(x_179);
if (x_198 == 0)
{
x_192 = x_179;
x_193 = x_198;
goto block_197;
}
else
{
lean_inc(x_191);
lean_dec(x_179);
x_192 = lean_box(0);
x_193 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_194; 
if (x_193 == 0)
{
x_194 = x_192;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_191);
x_194 = x_196;
goto block_195;
}
block_195:
{
return x_194;
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; uint8_t x_206; 
lean_dec_ref(x_170);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_199 = lean_ctor_get(x_174, 0);
x_206 = !lean_is_exclusive(x_174);
if (x_206 == 0)
{
x_200 = x_174;
x_201 = x_206;
goto block_205;
}
else
{
lean_inc(x_199);
lean_dec(x_174);
x_200 = lean_box(0);
x_201 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_202; 
if (x_201 == 0)
{
x_202 = x_200;
goto block_203;
}
else
{
lean_object* x_204; 
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_199);
x_202 = x_204;
goto block_203;
}
block_203:
{
return x_202;
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_168);
lean_dec(x_35);
lean_dec(x_31);
lean_dec_ref(x_1);
x_207 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__2);
x_208 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(x_207, x_4, x_5, x_6, x_7, x_8, x_9);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_216; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_209 = lean_ctor_get(x_167, 0);
x_216 = !lean_is_exclusive(x_167);
if (x_216 == 0)
{
x_210 = x_167;
x_211 = x_216;
goto block_215;
}
else
{
lean_inc(x_209);
lean_dec(x_167);
x_210 = lean_box(0);
x_211 = x_216;
goto block_215;
}
block_215:
{
lean_object* x_212; 
if (x_211 == 0)
{
x_212 = x_210;
goto block_213;
}
else
{
lean_object* x_214; 
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_209);
x_212 = x_214;
goto block_213;
}
block_213:
{
return x_212;
}
}
}
}
case 10:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_del_object(x_36);
lean_del_object(x_32);
lean_del_object(x_15);
lean_dec(x_14);
x_217 = lean_ctor_get(x_58, 0);
x_218 = lean_ctor_get(x_58, 1);
lean_inc(x_217);
x_219 = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(x_217, x_9);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec_ref(x_219);
if (lean_obj_tag(x_220) == 1)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_requiresBoxedVersion___redArg(x_221, x_9);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_260; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec_ref(x_222);
x_224 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
x_260 = lean_unbox(x_223);
lean_dec(x_223);
if (x_260 == 0)
{
lean_inc(x_217);
x_225 = x_217;
goto block_259;
}
else
{
lean_object* x_261; 
lean_inc(x_217);
x_261 = l_Lean_Compiler_LCNF_mkBoxedName(x_217);
x_225 = x_261;
goto block_259;
}
block_259:
{
lean_object* x_226; 
lean_inc(x_7);
x_226 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(x_218, x_224, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updatePapImp(x_17, x_58, x_225, x_228);
x_231 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_17, x_31, x_230, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_231) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; size_t x_235; size_t x_236; uint8_t x_237; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec_ref(x_231);
x_233 = lean_ctor_get(x_1, 0);
x_234 = lean_ctor_get(x_1, 1);
x_235 = lean_ptr_addr(x_234);
x_236 = lean_ptr_addr(x_35);
x_237 = lean_usize_dec_eq(x_235, x_236);
if (x_237 == 0)
{
x_38 = x_232;
x_39 = x_229;
x_40 = x_237;
goto block_42;
}
else
{
size_t x_238; size_t x_239; uint8_t x_240; 
x_238 = lean_ptr_addr(x_233);
x_239 = lean_ptr_addr(x_232);
x_240 = lean_usize_dec_eq(x_238, x_239);
x_38 = x_232;
x_39 = x_229;
x_40 = x_240;
goto block_42;
}
}
else
{
lean_object* x_241; lean_object* x_242; 
lean_dec_ref(x_231);
lean_dec(x_35);
lean_dec_ref(x_1);
x_241 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
x_242 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(x_241);
x_25 = x_229;
x_26 = x_242;
goto block_29;
}
}
else
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; uint8_t x_250; 
lean_dec(x_229);
lean_dec(x_35);
lean_dec_ref(x_1);
x_243 = lean_ctor_get(x_231, 0);
x_250 = !lean_is_exclusive(x_231);
if (x_250 == 0)
{
x_244 = x_231;
x_245 = x_250;
goto block_249;
}
else
{
lean_inc(x_243);
lean_dec(x_231);
x_244 = lean_box(0);
x_245 = x_250;
goto block_249;
}
block_249:
{
lean_object* x_246; 
if (x_245 == 0)
{
x_246 = x_244;
goto block_247;
}
else
{
lean_object* x_248; 
x_248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_248, 0, x_243);
x_246 = x_248;
goto block_247;
}
block_247:
{
return x_246;
}
}
}
}
else
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_258; 
lean_dec(x_225);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_7);
lean_dec_ref(x_1);
x_251 = lean_ctor_get(x_226, 0);
x_258 = !lean_is_exclusive(x_226);
if (x_258 == 0)
{
x_252 = x_226;
x_253 = x_258;
goto block_257;
}
else
{
lean_inc(x_251);
lean_dec(x_226);
x_252 = lean_box(0);
x_253 = x_258;
goto block_257;
}
block_257:
{
lean_object* x_254; 
if (x_253 == 0)
{
x_254 = x_252;
goto block_255;
}
else
{
lean_object* x_256; 
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_251);
x_254 = x_256;
goto block_255;
}
block_255:
{
return x_254;
}
}
}
}
}
else
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; uint8_t x_269; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_262 = lean_ctor_get(x_222, 0);
x_269 = !lean_is_exclusive(x_222);
if (x_269 == 0)
{
x_263 = x_222;
x_264 = x_269;
goto block_268;
}
else
{
lean_inc(x_262);
lean_dec(x_222);
x_263 = lean_box(0);
x_264 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_265; 
if (x_264 == 0)
{
x_265 = x_263;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_262);
x_265 = x_267;
goto block_266;
}
block_266:
{
return x_265;
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_220);
lean_dec(x_35);
lean_dec(x_31);
lean_dec_ref(x_1);
x_270 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__3);
x_271 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(x_270, x_4, x_5, x_6, x_7, x_8, x_9);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; uint8_t x_274; uint8_t x_279; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_272 = lean_ctor_get(x_219, 0);
x_279 = !lean_is_exclusive(x_219);
if (x_279 == 0)
{
x_273 = x_219;
x_274 = x_279;
goto block_278;
}
else
{
lean_inc(x_272);
lean_dec(x_219);
x_273 = lean_box(0);
x_274 = x_279;
goto block_278;
}
block_278:
{
lean_object* x_275; 
if (x_274 == 0)
{
x_275 = x_273;
goto block_276;
}
else
{
lean_object* x_277; 
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_272);
x_275 = x_277;
goto block_276;
}
block_276:
{
return x_275;
}
}
}
}
case 12:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_del_object(x_36);
lean_del_object(x_32);
lean_del_object(x_15);
lean_dec(x_14);
x_280 = lean_ctor_get(x_58, 2);
x_281 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__0));
lean_inc(x_7);
x_282 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(x_280, x_281, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; uint8_t x_325; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
lean_dec_ref(x_282);
x_284 = lean_ctor_get(x_283, 0);
x_285 = lean_ctor_get(x_283, 1);
x_325 = !lean_is_exclusive(x_283);
if (x_325 == 0)
{
x_286 = x_283;
x_287 = x_325;
goto block_324;
}
else
{
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_283);
x_286 = lean_box(0);
x_287 = x_325;
goto block_324;
}
block_324:
{
lean_object* x_288; lean_object* x_289; 
lean_inc_ref(x_58);
x_288 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_17, x_58, x_284);
x_289 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_17, x_31, x_288, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_315; 
x_290 = lean_ctor_get(x_289, 0);
x_315 = !lean_is_exclusive(x_289);
if (x_315 == 0)
{
x_291 = x_289;
x_292 = x_315;
goto block_314;
}
else
{
lean_inc(x_290);
lean_dec(x_289);
x_291 = lean_box(0);
x_292 = x_315;
goto block_314;
}
block_314:
{
lean_object* x_293; uint8_t x_299; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_304; lean_object* x_305; size_t x_306; size_t x_307; uint8_t x_308; 
x_304 = lean_ctor_get(x_1, 0);
x_305 = lean_ctor_get(x_1, 1);
x_306 = lean_ptr_addr(x_305);
x_307 = lean_ptr_addr(x_35);
x_308 = lean_usize_dec_eq(x_306, x_307);
if (x_308 == 0)
{
x_299 = x_308;
goto block_303;
}
else
{
size_t x_309; size_t x_310; uint8_t x_311; 
x_309 = lean_ptr_addr(x_304);
x_310 = lean_ptr_addr(x_290);
x_311 = lean_usize_dec_eq(x_309, x_310);
x_299 = x_311;
goto block_303;
}
}
else
{
lean_object* x_312; lean_object* x_313; 
lean_dec(x_290);
lean_del_object(x_286);
lean_dec(x_35);
lean_dec_ref(x_1);
x_312 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
x_313 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(x_312);
x_293 = x_313;
goto block_298;
}
block_298:
{
lean_object* x_294; lean_object* x_295; 
x_294 = l_Lean_Compiler_LCNF_attachCodeDecls(x_17, x_285, x_293);
lean_dec(x_285);
if (x_292 == 0)
{
lean_ctor_set(x_291, 0, x_294);
x_295 = x_291;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_297, 0, x_294);
x_295 = x_297;
goto block_296;
}
block_296:
{
return x_295;
}
}
block_303:
{
if (x_299 == 0)
{
lean_object* x_300; 
lean_dec_ref(x_1);
if (x_287 == 0)
{
lean_ctor_set(x_286, 1, x_35);
lean_ctor_set(x_286, 0, x_290);
x_300 = x_286;
goto block_301;
}
else
{
lean_object* x_302; 
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_290);
lean_ctor_set(x_302, 1, x_35);
x_300 = x_302;
goto block_301;
}
block_301:
{
x_293 = x_300;
goto block_298;
}
}
else
{
lean_dec(x_290);
lean_del_object(x_286);
lean_dec(x_35);
x_293 = x_1;
goto block_298;
}
}
}
}
else
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; uint8_t x_323; 
lean_del_object(x_286);
lean_dec(x_285);
lean_dec(x_35);
lean_dec_ref(x_1);
x_316 = lean_ctor_get(x_289, 0);
x_323 = !lean_is_exclusive(x_289);
if (x_323 == 0)
{
x_317 = x_289;
x_318 = x_323;
goto block_322;
}
else
{
lean_inc(x_316);
lean_dec(x_289);
x_317 = lean_box(0);
x_318 = x_323;
goto block_322;
}
block_322:
{
lean_object* x_319; 
if (x_318 == 0)
{
x_319 = x_317;
goto block_320;
}
else
{
lean_object* x_321; 
x_321 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_321, 0, x_316);
x_319 = x_321;
goto block_320;
}
block_320:
{
return x_319;
}
}
}
}
}
else
{
lean_object* x_326; lean_object* x_327; uint8_t x_328; uint8_t x_333; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_7);
lean_dec_ref(x_1);
x_326 = lean_ctor_get(x_282, 0);
x_333 = !lean_is_exclusive(x_282);
if (x_333 == 0)
{
x_327 = x_282;
x_328 = x_333;
goto block_332;
}
else
{
lean_inc(x_326);
lean_dec(x_282);
x_327 = lean_box(0);
x_328 = x_333;
goto block_332;
}
block_332:
{
lean_object* x_329; 
if (x_328 == 0)
{
x_329 = x_327;
goto block_330;
}
else
{
lean_object* x_331; 
x_331 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_331, 0, x_326);
x_329 = x_331;
goto block_330;
}
block_330:
{
return x_329;
}
}
}
}
case 13:
{
lean_object* x_334; lean_object* x_335; 
lean_del_object(x_36);
lean_dec(x_35);
lean_del_object(x_32);
lean_dec(x_31);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec_ref(x_1);
x_334 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4);
x_335 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(x_334, x_4, x_5, x_6, x_7, x_8, x_9);
return x_335;
}
case 14:
{
lean_object* x_336; lean_object* x_337; 
lean_del_object(x_36);
lean_dec(x_35);
lean_del_object(x_32);
lean_dec(x_31);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec_ref(x_1);
x_336 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4);
x_337 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(x_336, x_4, x_5, x_6, x_7, x_8, x_9);
return x_337;
}
case 15:
{
lean_object* x_338; lean_object* x_339; 
lean_del_object(x_36);
lean_dec(x_35);
lean_del_object(x_32);
lean_dec(x_31);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec_ref(x_1);
x_338 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___closed__4);
x_339 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(x_338, x_4, x_5, x_6, x_7, x_8, x_9);
return x_339;
}
default: 
{
lean_object* x_340; 
lean_inc(x_58);
lean_del_object(x_36);
lean_del_object(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_340 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(x_17, x_31, x_14, x_58, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; uint8_t x_343; uint8_t x_367; 
x_341 = lean_ctor_get(x_340, 0);
x_367 = !lean_is_exclusive(x_340);
if (x_367 == 0)
{
x_342 = x_340;
x_343 = x_367;
goto block_366;
}
else
{
lean_inc(x_341);
lean_dec(x_340);
x_342 = lean_box(0);
x_343 = x_367;
goto block_366;
}
block_366:
{
uint8_t x_344; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_353; lean_object* x_354; size_t x_355; size_t x_356; uint8_t x_357; 
lean_del_object(x_32);
x_353 = lean_ctor_get(x_1, 0);
x_354 = lean_ctor_get(x_1, 1);
x_355 = lean_ptr_addr(x_354);
x_356 = lean_ptr_addr(x_35);
x_357 = lean_usize_dec_eq(x_355, x_356);
if (x_357 == 0)
{
x_344 = x_357;
goto block_352;
}
else
{
size_t x_358; size_t x_359; uint8_t x_360; 
x_358 = lean_ptr_addr(x_353);
x_359 = lean_ptr_addr(x_341);
x_360 = lean_usize_dec_eq(x_358, x_359);
x_344 = x_360;
goto block_352;
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_del_object(x_342);
lean_dec(x_341);
lean_dec(x_35);
lean_dec_ref(x_1);
x_361 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__3);
x_362 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded_spec__0(x_361);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_362);
x_363 = x_32;
goto block_364;
}
else
{
lean_object* x_365; 
x_365 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_365, 0, x_362);
x_363 = x_365;
goto block_364;
}
block_364:
{
return x_363;
}
}
block_352:
{
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; 
lean_dec_ref(x_1);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_341);
lean_ctor_set(x_345, 1, x_35);
if (x_343 == 0)
{
lean_ctor_set(x_342, 0, x_345);
x_346 = x_342;
goto block_347;
}
else
{
lean_object* x_348; 
x_348 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_348, 0, x_345);
x_346 = x_348;
goto block_347;
}
block_347:
{
return x_346;
}
}
else
{
lean_object* x_349; 
lean_dec(x_341);
lean_dec(x_35);
if (x_343 == 0)
{
lean_ctor_set(x_342, 0, x_1);
x_349 = x_342;
goto block_350;
}
else
{
lean_object* x_351; 
x_351 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_351, 0, x_1);
x_349 = x_351;
goto block_350;
}
block_350:
{
return x_349;
}
}
}
}
}
else
{
lean_object* x_368; lean_object* x_369; uint8_t x_370; uint8_t x_375; 
lean_dec(x_35);
lean_del_object(x_32);
lean_dec_ref(x_1);
x_368 = lean_ctor_get(x_340, 0);
x_375 = !lean_is_exclusive(x_340);
if (x_375 == 0)
{
x_369 = x_340;
x_370 = x_375;
goto block_374;
}
else
{
lean_inc(x_368);
lean_dec(x_340);
x_369 = lean_box(0);
x_370 = x_375;
goto block_374;
}
block_374:
{
lean_object* x_371; 
if (x_370 == 0)
{
x_371 = x_369;
goto block_372;
}
else
{
lean_object* x_373; 
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_368);
x_371 = x_373;
goto block_372;
}
block_372:
{
return x_371;
}
}
}
}
}
block_42:
{
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec_ref(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_35);
x_25 = x_39;
x_26 = x_41;
goto block_29;
}
else
{
lean_dec_ref(x_38);
lean_dec(x_35);
x_25 = x_39;
x_26 = x_1;
goto block_29;
}
}
block_52:
{
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_35);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_45);
x_46 = x_36;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
else
{
lean_object* x_49; 
lean_dec_ref(x_43);
lean_dec(x_35);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_1);
x_49 = x_36;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_1);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
block_57:
{
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec_ref(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_35);
x_18 = x_54;
x_19 = x_56;
goto block_24;
}
else
{
lean_dec_ref(x_53);
lean_dec(x_35);
x_18 = x_54;
x_19 = x_1;
goto block_24;
}
}
}
}
else
{
lean_del_object(x_32);
lean_dec(x_31);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_34;
}
}
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_387; 
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_380 = lean_ctor_get(x_30, 0);
x_387 = !lean_is_exclusive(x_30);
if (x_387 == 0)
{
x_381 = x_30;
x_382 = x_387;
goto block_386;
}
else
{
lean_inc(x_380);
lean_dec(x_30);
x_381 = lean_box(0);
x_382 = x_387;
goto block_386;
}
block_386:
{
lean_object* x_383; 
if (x_382 == 0)
{
x_383 = x_381;
goto block_384;
}
else
{
lean_object* x_385; 
x_385 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_385, 0, x_380);
x_383 = x_385;
goto block_384;
}
block_384:
{
return x_383;
}
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Compiler_LCNF_attachCodeDecls(x_17, x_18, x_19);
lean_dec_ref(x_18);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_20);
x_21 = x_15;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Compiler_LCNF_attachCodeDecls(x_17, x_25, x_26);
lean_dec_ref(x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; uint8_t x_397; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_390 = lean_ctor_get(x_13, 0);
x_397 = !lean_is_exclusive(x_13);
if (x_397 == 0)
{
x_391 = x_13;
x_392 = x_397;
goto block_396;
}
else
{
lean_inc(x_390);
lean_dec(x_13);
x_391 = lean_box(0);
x_392 = x_397;
goto block_396;
}
block_396:
{
lean_object* x_393; 
if (x_392 == 0)
{
x_393 = x_391;
goto block_394;
}
else
{
lean_object* x_395; 
x_395 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_395, 0, x_390);
x_393 = x_395;
goto block_394;
}
block_394:
{
return x_393;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
x_2 = lean_unsigned_to_nat(44u);
x_3 = lean_unsigned_to_nat(284u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_unboxResultIfNeeded___redArg___closed__2));
x_2 = lean_unsigned_to_nat(59u);
x_3 = lean_unsigned_to_nat(287u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__9));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
x_11 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_12, 2);
x_15 = lean_ctor_get(x_12, 4);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_15);
x_16 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(x_15, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_2, 1);
x_19 = 1;
lean_inc_ref(x_14);
lean_inc_ref(x_18);
lean_inc_ref(x_12);
x_20 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_19, x_12, x_18, x_14, x_17, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc_ref(x_13);
x_22 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_50; 
x_23 = lean_ctor_get(x_22, 0);
x_50 = !lean_is_exclusive(x_22);
if (x_50 == 0)
{
x_24 = x_22;
x_25 = x_50;
goto block_49;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_50;
goto block_49;
}
block_49:
{
uint8_t x_26; size_t x_43; size_t x_44; uint8_t x_45; 
x_43 = lean_ptr_addr(x_13);
x_44 = lean_ptr_addr(x_23);
x_45 = lean_usize_dec_eq(x_43, x_44);
if (x_45 == 0)
{
x_26 = x_45;
goto block_42;
}
else
{
size_t x_46; size_t x_47; uint8_t x_48; 
x_46 = lean_ptr_addr(x_12);
x_47 = lean_ptr_addr(x_21);
x_48 = lean_usize_dec_eq(x_46, x_47);
x_26 = x_48;
goto block_42;
}
block_42:
{
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_1, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_1, 0);
lean_dec(x_38);
x_27 = x_1;
x_28 = x_36;
goto block_35;
}
else
{
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_29; 
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 0, x_21);
x_29 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_23);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_29);
x_30 = x_24;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_23);
lean_dec(x_21);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_1);
x_39 = x_24;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_1);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
else
{
lean_dec(x_21);
lean_dec_ref(x_1);
return x_22;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_51 = lean_ctor_get(x_20, 0);
x_58 = !lean_is_exclusive(x_20);
if (x_58 == 0)
{
x_52 = x_20;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_20);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
else
{
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_16;
}
}
case 3:
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
x_61 = 1;
x_62 = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(x_61, x_59, x_5);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
if (lean_obj_tag(x_63) == 1)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_ctor_get(x_64, 2);
lean_inc_ref(x_65);
lean_dec(x_64);
x_66 = lean_box(x_61);
x_67 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__0___boxed), 3, 2);
lean_closure_set(x_67, 0, x_66);
lean_closure_set(x_67, 1, x_65);
x_68 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_castArgsIfNeededAux(x_60, x_67, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_96; 
x_69 = lean_ctor_get(x_68, 0);
x_96 = !lean_is_exclusive(x_68);
if (x_96 == 0)
{
x_70 = x_68;
x_71 = x_96;
goto block_95;
}
else
{
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
x_71 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_80; uint8_t x_91; 
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_91 = l_Lean_instBEqFVarId_beq(x_59, x_59);
if (x_91 == 0)
{
x_80 = x_91;
goto block_90;
}
else
{
size_t x_92; size_t x_93; uint8_t x_94; 
x_92 = lean_ptr_addr(x_60);
x_93 = lean_ptr_addr(x_72);
x_94 = lean_usize_dec_eq(x_92, x_93);
x_80 = x_94;
goto block_90;
}
block_79:
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Lean_Compiler_LCNF_attachCodeDecls(x_61, x_73, x_74);
lean_dec(x_73);
if (x_71 == 0)
{
lean_ctor_set(x_70, 0, x_75);
x_76 = x_70;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_75);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
block_90:
{
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; uint8_t x_87; 
lean_inc(x_59);
x_87 = !lean_is_exclusive(x_1);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_1, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_1, 0);
lean_dec(x_89);
x_81 = x_1;
x_82 = x_87;
goto block_86;
}
else
{
lean_dec(x_1);
x_81 = lean_box(0);
x_82 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_83; 
if (x_82 == 0)
{
lean_ctor_set(x_81, 1, x_72);
x_83 = x_81;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_85, 0, x_59);
lean_ctor_set(x_85, 1, x_72);
x_83 = x_85;
goto block_84;
}
block_84:
{
x_74 = x_83;
goto block_79;
}
}
}
else
{
lean_dec(x_72);
x_74 = x_1;
goto block_79;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_104; 
lean_dec_ref(x_1);
x_97 = lean_ctor_get(x_68, 0);
x_104 = !lean_is_exclusive(x_68);
if (x_104 == 0)
{
x_98 = x_68;
x_99 = x_104;
goto block_103;
}
else
{
lean_inc(x_97);
lean_dec(x_68);
x_98 = lean_box(0);
x_99 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_100; 
if (x_99 == 0)
{
x_100 = x_98;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_97);
x_100 = x_102;
goto block_101;
}
block_101:
{
return x_100;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_63);
lean_dec_ref(x_1);
x_105 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__1);
x_106 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(x_105, x_2, x_3, x_4, x_5, x_6, x_7);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_114; 
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_107 = lean_ctor_get(x_62, 0);
x_114 = !lean_is_exclusive(x_62);
if (x_114 == 0)
{
x_108 = x_62;
x_109 = x_114;
goto block_113;
}
else
{
lean_inc(x_107);
lean_dec(x_62);
x_108 = lean_box(0);
x_109 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_110; 
if (x_109 == 0)
{
x_110 = x_108;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_107);
x_110 = x_112;
goto block_111;
}
block_111:
{
return x_110;
}
}
}
}
case 4:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_1, 0);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_115, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 3);
lean_inc_ref(x_119);
x_120 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_119);
x_121 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(x_120, x_119, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
lean_inc(x_118);
x_123 = l_Lean_Compiler_LCNF_getType(x_118, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = lean_box(0);
lean_inc(x_116);
x_126 = l_Lean_mkConst(x_116, x_125);
x_127 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(x_124, x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_126);
lean_inc(x_118);
x_128 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(x_118, x_124, x_126, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
x_130 = 1;
x_131 = lean_box(0);
x_132 = l_Lean_Compiler_LCNF_mkLetDecl(x_130, x_131, x_126, x_129, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(x_116, x_122, x_118, x_1, x_119, x_117, x_134, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_117);
lean_dec_ref(x_119);
lean_dec(x_118);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_144; 
x_136 = lean_ctor_get(x_135, 0);
x_144 = !lean_is_exclusive(x_135);
if (x_144 == 0)
{
x_137 = x_135;
x_138 = x_144;
goto block_143;
}
else
{
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_box(0);
x_138 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_136);
if (x_138 == 0)
{
lean_ctor_set(x_137, 0, x_139);
x_140 = x_137;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_139);
x_140 = x_142;
goto block_141;
}
block_141:
{
return x_140;
}
}
}
else
{
lean_dec(x_133);
return x_135;
}
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_152; 
lean_dec(x_122);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_145 = lean_ctor_get(x_132, 0);
x_152 = !lean_is_exclusive(x_132);
if (x_152 == 0)
{
x_146 = x_132;
x_147 = x_152;
goto block_151;
}
else
{
lean_inc(x_145);
lean_dec(x_132);
x_146 = lean_box(0);
x_147 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_148; 
if (x_147 == 0)
{
x_148 = x_146;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_145);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_160; 
lean_dec_ref(x_126);
lean_dec(x_122);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_153 = lean_ctor_get(x_128, 0);
x_160 = !lean_is_exclusive(x_128);
if (x_160 == 0)
{
x_154 = x_128;
x_155 = x_160;
goto block_159;
}
else
{
lean_inc(x_153);
lean_dec(x_128);
x_154 = lean_box(0);
x_155 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_156; 
if (x_155 == 0)
{
x_156 = x_154;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_153);
x_156 = x_158;
goto block_157;
}
block_157:
{
return x_156;
}
}
}
}
else
{
lean_object* x_161; 
lean_dec_ref(x_126);
lean_dec(x_124);
lean_inc(x_118);
x_161 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__1(x_116, x_122, x_118, x_1, x_119, x_117, x_118, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_117);
lean_dec_ref(x_119);
lean_dec(x_118);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; uint8_t x_169; 
lean_dec(x_122);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_162 = lean_ctor_get(x_123, 0);
x_169 = !lean_is_exclusive(x_123);
if (x_169 == 0)
{
x_163 = x_123;
x_164 = x_169;
goto block_168;
}
else
{
lean_inc(x_162);
lean_dec(x_123);
x_163 = lean_box(0);
x_164 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_165; 
if (x_164 == 0)
{
x_165 = x_163;
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_162);
x_165 = x_167;
goto block_166;
}
block_166:
{
return x_165;
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_177; 
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_170 = lean_ctor_get(x_121, 0);
x_177 = !lean_is_exclusive(x_121);
if (x_177 == 0)
{
x_171 = x_121;
x_172 = x_177;
goto block_176;
}
else
{
lean_inc(x_170);
lean_dec(x_121);
x_171 = lean_box(0);
x_172 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_173; 
if (x_172 == 0)
{
x_173 = x_171;
goto block_174;
}
else
{
lean_object* x_175; 
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_170);
x_173 = x_175;
goto block_174;
}
block_174:
{
return x_173;
}
}
}
}
case 5:
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_1, 0);
lean_inc(x_178);
lean_inc(x_178);
x_179 = l_Lean_Compiler_LCNF_getType(x_178, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec_ref(x_179);
x_181 = lean_ctor_get(x_2, 1);
x_182 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(x_180, x_181);
if (x_182 == 0)
{
lean_object* x_183; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_181);
lean_inc(x_178);
x_183 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(x_178, x_180, x_181, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = 1;
x_186 = lean_box(0);
lean_inc_ref(x_181);
x_187 = l_Lean_Compiler_LCNF_mkLetDecl(x_185, x_186, x_181, x_184, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; uint8_t x_205; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(x_178, x_1, x_189, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_178);
x_205 = !lean_is_exclusive(x_2);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_2, 1);
lean_dec(x_206);
x_207 = lean_ctor_get(x_2, 0);
lean_dec(x_207);
x_191 = x_2;
x_192 = x_205;
goto block_204;
}
else
{
lean_dec(x_2);
x_191 = lean_box(0);
x_192 = x_205;
goto block_204;
}
block_204:
{
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_203; 
x_193 = lean_ctor_get(x_190, 0);
x_203 = !lean_is_exclusive(x_190);
if (x_203 == 0)
{
x_194 = x_190;
x_195 = x_203;
goto block_202;
}
else
{
lean_inc(x_193);
lean_dec(x_190);
x_194 = lean_box(0);
x_195 = x_203;
goto block_202;
}
block_202:
{
lean_object* x_196; 
if (x_192 == 0)
{
lean_ctor_set(x_191, 1, x_193);
lean_ctor_set(x_191, 0, x_188);
x_196 = x_191;
goto block_200;
}
else
{
lean_object* x_201; 
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_188);
lean_ctor_set(x_201, 1, x_193);
x_196 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_197; 
if (x_195 == 0)
{
lean_ctor_set(x_194, 0, x_196);
x_197 = x_194;
goto block_198;
}
else
{
lean_object* x_199; 
x_199 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_199, 0, x_196);
x_197 = x_199;
goto block_198;
}
block_198:
{
return x_197;
}
}
}
}
else
{
lean_del_object(x_191);
lean_dec(x_188);
return x_190;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_215; 
lean_dec(x_178);
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_208 = lean_ctor_get(x_187, 0);
x_215 = !lean_is_exclusive(x_187);
if (x_215 == 0)
{
x_209 = x_187;
x_210 = x_215;
goto block_214;
}
else
{
lean_inc(x_208);
lean_dec(x_187);
x_209 = lean_box(0);
x_210 = x_215;
goto block_214;
}
block_214:
{
lean_object* x_211; 
if (x_210 == 0)
{
x_211 = x_209;
goto block_212;
}
else
{
lean_object* x_213; 
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_208);
x_211 = x_213;
goto block_212;
}
block_212:
{
return x_211;
}
}
}
}
else
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; uint8_t x_223; 
lean_dec_ref(x_1);
lean_dec(x_178);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_216 = lean_ctor_get(x_183, 0);
x_223 = !lean_is_exclusive(x_183);
if (x_223 == 0)
{
x_217 = x_183;
x_218 = x_223;
goto block_222;
}
else
{
lean_inc(x_216);
lean_dec(x_183);
x_217 = lean_box(0);
x_218 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_219; 
if (x_218 == 0)
{
x_219 = x_217;
goto block_220;
}
else
{
lean_object* x_221; 
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_216);
x_219 = x_221;
goto block_220;
}
block_220:
{
return x_219;
}
}
}
}
else
{
lean_object* x_224; 
lean_dec(x_180);
lean_inc(x_178);
x_224 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__2(x_178, x_1, x_178, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_178);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; uint8_t x_232; 
lean_dec_ref(x_1);
lean_dec(x_178);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_225 = lean_ctor_get(x_179, 0);
x_232 = !lean_is_exclusive(x_179);
if (x_232 == 0)
{
x_226 = x_179;
x_227 = x_232;
goto block_231;
}
else
{
lean_inc(x_225);
lean_dec(x_179);
x_226 = lean_box(0);
x_227 = x_232;
goto block_231;
}
block_231:
{
lean_object* x_228; 
if (x_227 == 0)
{
x_228 = x_226;
goto block_229;
}
else
{
lean_object* x_230; 
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_225);
x_228 = x_230;
goto block_229;
}
block_229:
{
return x_228;
}
}
}
}
case 6:
{
lean_object* x_233; lean_object* x_234; size_t x_235; size_t x_236; uint8_t x_237; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_233 = lean_ctor_get(x_1, 0);
x_234 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_234);
lean_dec_ref(x_2);
x_235 = lean_ptr_addr(x_233);
x_236 = lean_ptr_addr(x_234);
x_237 = lean_usize_dec_eq(x_235, x_236);
if (x_237 == 0)
{
lean_object* x_238; uint8_t x_239; uint8_t x_245; 
x_245 = !lean_is_exclusive(x_1);
if (x_245 == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_1, 0);
lean_dec(x_246);
x_238 = x_1;
x_239 = x_245;
goto block_244;
}
else
{
lean_dec(x_1);
x_238 = lean_box(0);
x_239 = x_245;
goto block_244;
}
block_244:
{
lean_object* x_240; 
if (x_239 == 0)
{
lean_ctor_set(x_238, 0, x_234);
x_240 = x_238;
goto block_242;
}
else
{
lean_object* x_243; 
x_243 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_243, 0, x_234);
x_240 = x_243;
goto block_242;
}
block_242:
{
lean_object* x_241; 
x_241 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_241, 0, x_240);
return x_241;
}
}
}
else
{
lean_object* x_247; 
lean_dec_ref(x_234);
x_247 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_247, 0, x_1);
return x_247;
}
}
case 8:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_248 = lean_ctor_get(x_1, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_1, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_1, 2);
lean_inc(x_250);
x_251 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_251);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_251);
x_252 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(x_251, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
lean_inc(x_250);
x_254 = l_Lean_Compiler_LCNF_getType(x_250, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_tryCorrectLetDeclType___closed__8);
x_257 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(x_255, x_256);
if (x_257 == 0)
{
lean_object* x_258; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
lean_inc(x_250);
x_258 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(x_250, x_255, x_256, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec_ref(x_258);
x_260 = 1;
x_261 = lean_box(0);
x_262 = l_Lean_Compiler_LCNF_mkLetDecl(x_260, x_261, x_256, x_259, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_dec_ref(x_262);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(x_248, x_249, x_253, x_250, x_251, x_1, x_264, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_251);
lean_dec(x_250);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; uint8_t x_274; 
x_266 = lean_ctor_get(x_265, 0);
x_274 = !lean_is_exclusive(x_265);
if (x_274 == 0)
{
x_267 = x_265;
x_268 = x_274;
goto block_273;
}
else
{
lean_inc(x_266);
lean_dec(x_265);
x_267 = lean_box(0);
x_268 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_263);
lean_ctor_set(x_269, 1, x_266);
if (x_268 == 0)
{
lean_ctor_set(x_267, 0, x_269);
x_270 = x_267;
goto block_271;
}
else
{
lean_object* x_272; 
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_269);
x_270 = x_272;
goto block_271;
}
block_271:
{
return x_270;
}
}
}
else
{
lean_dec(x_263);
return x_265;
}
}
else
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; uint8_t x_282; 
lean_dec(x_253);
lean_dec_ref(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_275 = lean_ctor_get(x_262, 0);
x_282 = !lean_is_exclusive(x_262);
if (x_282 == 0)
{
x_276 = x_262;
x_277 = x_282;
goto block_281;
}
else
{
lean_inc(x_275);
lean_dec(x_262);
x_276 = lean_box(0);
x_277 = x_282;
goto block_281;
}
block_281:
{
lean_object* x_278; 
if (x_277 == 0)
{
x_278 = x_276;
goto block_279;
}
else
{
lean_object* x_280; 
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_275);
x_278 = x_280;
goto block_279;
}
block_279:
{
return x_278;
}
}
}
}
else
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; uint8_t x_290; 
lean_dec(x_253);
lean_dec_ref(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_283 = lean_ctor_get(x_258, 0);
x_290 = !lean_is_exclusive(x_258);
if (x_290 == 0)
{
x_284 = x_258;
x_285 = x_290;
goto block_289;
}
else
{
lean_inc(x_283);
lean_dec(x_258);
x_284 = lean_box(0);
x_285 = x_290;
goto block_289;
}
block_289:
{
lean_object* x_286; 
if (x_285 == 0)
{
x_286 = x_284;
goto block_287;
}
else
{
lean_object* x_288; 
x_288 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_288, 0, x_283);
x_286 = x_288;
goto block_287;
}
block_287:
{
return x_286;
}
}
}
}
else
{
lean_object* x_291; 
lean_dec(x_255);
lean_inc(x_250);
x_291 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__3(x_248, x_249, x_253, x_250, x_251, x_1, x_250, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_251);
lean_dec(x_250);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; uint8_t x_299; 
lean_dec(x_253);
lean_dec_ref(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_292 = lean_ctor_get(x_254, 0);
x_299 = !lean_is_exclusive(x_254);
if (x_299 == 0)
{
x_293 = x_254;
x_294 = x_299;
goto block_298;
}
else
{
lean_inc(x_292);
lean_dec(x_254);
x_293 = lean_box(0);
x_294 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_295; 
if (x_294 == 0)
{
x_295 = x_293;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_292);
x_295 = x_297;
goto block_296;
}
block_296:
{
return x_295;
}
}
}
}
else
{
lean_dec_ref(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec_ref(x_1);
lean_dec(x_248);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_252;
}
}
case 9:
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_300 = lean_ctor_get(x_1, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_1, 1);
lean_inc(x_301);
x_302 = lean_ctor_get(x_1, 2);
lean_inc(x_302);
x_303 = lean_ctor_get(x_1, 3);
lean_inc(x_303);
x_304 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_304);
x_305 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_305);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_305);
x_306 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(x_305, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
lean_dec_ref(x_306);
lean_inc(x_303);
x_308 = l_Lean_Compiler_LCNF_getType(x_303, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
lean_dec_ref(x_308);
x_310 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_typesEqvForBoxing(x_309, x_304);
if (x_310 == 0)
{
lean_object* x_311; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_304);
lean_inc(x_303);
x_311 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_mkCast(x_303, x_309, x_304, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
lean_dec_ref(x_311);
x_313 = 1;
x_314 = lean_box(0);
lean_inc_ref(x_304);
x_315 = l_Lean_Compiler_LCNF_mkLetDecl(x_313, x_314, x_304, x_312, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec_ref(x_315);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(x_300, x_301, x_302, x_304, x_307, x_303, x_305, x_1, x_317, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_305);
lean_dec(x_303);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; uint8_t x_327; 
x_319 = lean_ctor_get(x_318, 0);
x_327 = !lean_is_exclusive(x_318);
if (x_327 == 0)
{
x_320 = x_318;
x_321 = x_327;
goto block_326;
}
else
{
lean_inc(x_319);
lean_dec(x_318);
x_320 = lean_box(0);
x_321 = x_327;
goto block_326;
}
block_326:
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_316);
lean_ctor_set(x_322, 1, x_319);
if (x_321 == 0)
{
lean_ctor_set(x_320, 0, x_322);
x_323 = x_320;
goto block_324;
}
else
{
lean_object* x_325; 
x_325 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_325, 0, x_322);
x_323 = x_325;
goto block_324;
}
block_324:
{
return x_323;
}
}
}
else
{
lean_dec(x_316);
return x_318;
}
}
else
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_335; 
lean_dec(x_307);
lean_dec_ref(x_305);
lean_dec_ref(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec_ref(x_1);
lean_dec(x_300);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_328 = lean_ctor_get(x_315, 0);
x_335 = !lean_is_exclusive(x_315);
if (x_335 == 0)
{
x_329 = x_315;
x_330 = x_335;
goto block_334;
}
else
{
lean_inc(x_328);
lean_dec(x_315);
x_329 = lean_box(0);
x_330 = x_335;
goto block_334;
}
block_334:
{
lean_object* x_331; 
if (x_330 == 0)
{
x_331 = x_329;
goto block_332;
}
else
{
lean_object* x_333; 
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_328);
x_331 = x_333;
goto block_332;
}
block_332:
{
return x_331;
}
}
}
}
else
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; uint8_t x_343; 
lean_dec(x_307);
lean_dec_ref(x_305);
lean_dec_ref(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec_ref(x_1);
lean_dec(x_300);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_336 = lean_ctor_get(x_311, 0);
x_343 = !lean_is_exclusive(x_311);
if (x_343 == 0)
{
x_337 = x_311;
x_338 = x_343;
goto block_342;
}
else
{
lean_inc(x_336);
lean_dec(x_311);
x_337 = lean_box(0);
x_338 = x_343;
goto block_342;
}
block_342:
{
lean_object* x_339; 
if (x_338 == 0)
{
x_339 = x_337;
goto block_340;
}
else
{
lean_object* x_341; 
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_336);
x_339 = x_341;
goto block_340;
}
block_340:
{
return x_339;
}
}
}
}
else
{
lean_object* x_344; 
lean_dec(x_309);
lean_inc(x_303);
x_344 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___lam__4(x_300, x_301, x_302, x_304, x_307, x_303, x_305, x_1, x_303, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_305);
lean_dec(x_303);
return x_344;
}
}
else
{
lean_object* x_345; lean_object* x_346; uint8_t x_347; uint8_t x_352; 
lean_dec(x_307);
lean_dec_ref(x_305);
lean_dec_ref(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec_ref(x_1);
lean_dec(x_300);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_345 = lean_ctor_get(x_308, 0);
x_352 = !lean_is_exclusive(x_308);
if (x_352 == 0)
{
x_346 = x_308;
x_347 = x_352;
goto block_351;
}
else
{
lean_inc(x_345);
lean_dec(x_308);
x_346 = lean_box(0);
x_347 = x_352;
goto block_351;
}
block_351:
{
lean_object* x_348; 
if (x_347 == 0)
{
x_348 = x_346;
goto block_349;
}
else
{
lean_object* x_350; 
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_345);
x_348 = x_350;
goto block_349;
}
block_349:
{
return x_348;
}
}
}
}
else
{
lean_dec_ref(x_305);
lean_dec_ref(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec_ref(x_1);
lean_dec(x_300);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_306;
}
}
default: 
{
lean_object* x_353; lean_object* x_354; 
lean_dec_ref(x_1);
x_353 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___closed__2);
x_354 = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet_spec__0(x_353, x_2, x_3, x_4, x_5, x_6, x_7);
return x_354;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing___boxed), 8, 0);
x_14 = lean_array_fget_borrowed(x_2, x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_14);
x_15 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(x_14, x_13, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ptr_addr(x_14);
x_18 = lean_ptr_addr(x_16);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_1, x_20);
x_22 = lean_array_fset(x_2, x_1, x_16);
lean_dec(x_1);
x_1 = x_21;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_1, x_24);
lean_dec(x_1);
x_1 = x_25;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_15, 0);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
x_28 = x_15;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_visitLet(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing_spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_2, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uget(x_1, x_2);
x_17 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_65; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
x_20 = lean_ctor_get(x_16, 2);
x_65 = !lean_is_exclusive(x_16);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_16, 1);
lean_dec(x_66);
x_21 = x_16;
x_22 = x_65;
goto block_64;
}
else
{
lean_inc(x_20);
lean_inc(x_18);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_63; 
x_23 = lean_ctor_get(x_17, 0);
x_63 = !lean_is_exclusive(x_17);
if (x_63 == 0)
{
x_24 = x_17;
x_25 = x_63;
goto block_62;
}
else
{
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___closed__0));
x_27 = lean_st_mk_ref(x_26);
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 2);
lean_inc_ref(x_29);
lean_inc(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_27);
x_31 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_Code_explicitBoxing(x_23, x_30, x_27, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_st_ref_get(x_27);
lean_dec(x_27);
x_34 = 1;
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_32);
x_35 = x_24;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_32);
x_35 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_36; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_35);
x_36 = x_21;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_51, 0, x_18);
lean_ctor_set(x_51, 1, x_35);
lean_ctor_set(x_51, 2, x_20);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_19);
x_36 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_37; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_37 = l_Lean_Compiler_LCNF_Decl_elimDeadVars(x_34, x_36, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_39);
lean_dec(x_33);
x_40 = l_Array_append___redArg(x_4, x_39);
lean_dec_ref(x_39);
x_41 = lean_array_push(x_40, x_38);
x_10 = x_41;
goto block_14;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_33);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_42 = lean_ctor_get(x_37, 0);
x_49 = !lean_is_exclusive(x_37);
if (x_49 == 0)
{
x_43 = x_37;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_27);
lean_del_object(x_24);
lean_del_object(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_54 = lean_ctor_get(x_31, 0);
x_61 = !lean_is_exclusive(x_31);
if (x_61 == 0)
{
x_55 = x_31;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_31);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
else
{
lean_object* x_67; 
lean_dec_ref(x_17);
x_67 = lean_array_push(x_4, x_16);
x_10 = x_67;
goto block_14;
}
}
else
{
lean_object* x_68; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_4);
return x_68;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = ((lean_object*)(l_Array_filterMapM___at___00Lean_Compiler_LCNF_addBoxedVersions_spec__0___closed__0));
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_11, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_LCNF_addBoxedVersions(x_12, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
if (x_14 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Compiler_LCNF_addBoxedVersions(x_12, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_13);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(x_1, x_18, x_19, x_12, x_2, x_3, x_4, x_5);
x_7 = x_20;
goto block_10;
}
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_13);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run_spec__0(x_1, x_21, x_22, x_12, x_2, x_3, x_4, x_5);
x_7 = x_23;
goto block_10;
}
}
block_10:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_Compiler_LCNF_addBoxedVersions(x_8, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_run(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_));
x_3 = 1;
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_();
return x_2;
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
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Runtime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ExplicitBoxing_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitBoxing_654907530____hygCtx___hyg_2_()
;
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
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ElimDead(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Runtime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
}
#ifdef __cplusplus
}
#endif
