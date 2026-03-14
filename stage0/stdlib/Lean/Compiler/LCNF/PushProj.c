// Lean compiler output
// Module: Lean.Compiler.LCNF.PushProj
// Imports: public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.Internalize
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
size_t lean_usize_add(size_t, size_t);
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
lean_object* l_Lean_Compiler_LCNF_CodeDecl_collectUsed(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_collectUsed(uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instInhabitedFVarIdHashSet;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_pushProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pushProj"};
static const lean_object* l_Lean_Compiler_LCNF_pushProj___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_pushProj___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_pushProj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_pushProj___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 57, 226, 13, 246, 16, 24, 68)}};
static const lean_object* l_Lean_Compiler_LCNF_pushProj___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_pushProj___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_pushProj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_pushProj___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_pushProj___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_pushProj(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_pushProj___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 211, 73, 224, 17, 126, 75, 83)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PushProj"};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 179, 94, 9, 25, 163, 216, 24)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(135, 104, 144, 85, 27, 131, 153, 130)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 62, 249, 6, 203, 178, 151, 129)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 49, 110, 94, 60, 21, 8, 73)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(193, 29, 17, 122, 64, 36, 82, 205)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 219, 6, 144, 2, 95, 149, 99)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 33, 50, 123, 128, 141, 162, 66)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 113, 212, 180, 66, 7, 55, 229)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 184, 184, 55, 242, 203, 128, 85)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 137, 217, 130, 130, 74, 181, 200)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 138, 208, 235, 67, 188, 139, 202)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1777867010) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(222, 128, 220, 201, 112, 181, 25, 254)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 173, 233, 223, 159, 172, 112, 38)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 220, 201, 25, 124, 255, 4, 5)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(60, 4, 130, 51, 46, 50, 49, 200)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(lean_object* v_alt_1_, lean_object* v_f_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___y_9_; 
switch(lean_obj_tag(v_alt_1_))
{
case 0:
{
lean_object* v_code_28_; 
v_code_28_ = lean_ctor_get(v_alt_1_, 2);
lean_inc_ref(v_code_28_);
v___y_9_ = v_code_28_;
goto v___jp_8_;
}
case 1:
{
lean_object* v_code_29_; 
v_code_29_ = lean_ctor_get(v_alt_1_, 1);
lean_inc_ref(v_code_29_);
v___y_9_ = v_code_29_;
goto v___jp_8_;
}
default: 
{
lean_object* v_code_30_; 
v_code_30_ = lean_ctor_get(v_alt_1_, 0);
lean_inc_ref(v_code_30_);
v___y_9_ = v_code_30_;
goto v___jp_8_;
}
}
v___jp_8_:
{
lean_object* v___x_10_; 
v___x_10_ = lean_apply_6(v_f_2_, v___y_9_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_19_ == 0)
{
v___x_13_ = v___x_10_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_a_11_);
lean_dec(v___x_10_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
v___x_15_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1_, v_a_11_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
lean_dec_ref(v_alt_1_);
v_a_20_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_27_ == 0)
{
v___x_22_ = v___x_10_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_10_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_20_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg___boxed(lean_object* v_alt_31_, lean_object* v_f_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v_alt_31_, v_f_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1(uint8_t v_pu_39_, lean_object* v_alt_40_, lean_object* v_f_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v_alt_40_, v_f_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___boxed(lean_object* v_pu_48_, lean_object* v_alt_49_, lean_object* v_f_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
uint8_t v_pu_boxed_56_; lean_object* v_res_57_; 
v_pu_boxed_56_ = lean_unbox(v_pu_48_);
v_res_57_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1(v_pu_boxed_56_, v_alt_49_, v_f_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
return v_res_57_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(lean_object* v_a_58_, lean_object* v_x_59_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
uint8_t v___x_60_; 
v___x_60_ = 0;
return v___x_60_;
}
else
{
lean_object* v_key_61_; lean_object* v_tail_62_; uint8_t v___x_63_; 
v_key_61_ = lean_ctor_get(v_x_59_, 0);
v_tail_62_ = lean_ctor_get(v_x_59_, 2);
v___x_63_ = l_Lean_instBEqFVarId_beq(v_key_61_, v_a_58_);
if (v___x_63_ == 0)
{
v_x_59_ = v_tail_62_;
goto _start;
}
else
{
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_65_, lean_object* v_x_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_65_, v_x_66_);
lean_dec(v_x_66_);
lean_dec(v_a_65_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(lean_object* v_m_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_buckets_71_; lean_object* v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v_fold_76_; uint64_t v___x_77_; uint64_t v___x_78_; uint64_t v___x_79_; size_t v___x_80_; size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v_buckets_71_ = lean_ctor_get(v_m_69_, 1);
v___x_72_ = lean_array_get_size(v_buckets_71_);
v___x_73_ = l_Lean_instHashableFVarId_hash(v_a_70_);
v___x_74_ = 32ULL;
v___x_75_ = lean_uint64_shift_right(v___x_73_, v___x_74_);
v_fold_76_ = lean_uint64_xor(v___x_73_, v___x_75_);
v___x_77_ = 16ULL;
v___x_78_ = lean_uint64_shift_right(v_fold_76_, v___x_77_);
v___x_79_ = lean_uint64_xor(v_fold_76_, v___x_78_);
v___x_80_ = lean_uint64_to_usize(v___x_79_);
v___x_81_ = lean_usize_of_nat(v___x_72_);
v___x_82_ = ((size_t)1ULL);
v___x_83_ = lean_usize_sub(v___x_81_, v___x_82_);
v___x_84_ = lean_usize_land(v___x_80_, v___x_83_);
v___x_85_ = lean_array_uget_borrowed(v_buckets_71_, v___x_84_);
v___x_86_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_70_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg___boxed(lean_object* v_m_87_, lean_object* v_a_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_m_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_m_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0(lean_object* v_altsUsed_91_, lean_object* v_j_92_, lean_object* v_fvar_93_, lean_object* v_b_94_, uint8_t v___x_95_, lean_object* v_k_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_102_ = l_Lean_instInhabitedFVarIdHashSet;
v___x_103_ = lean_array_get_borrowed(v___x_102_, v_altsUsed_91_, v_j_92_);
v___x_104_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v___x_103_, v_fvar_93_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
lean_dec_ref(v_b_94_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v_k_96_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_mk_empty_array_with_capacity(v___x_106_);
v___x_108_ = lean_array_push(v___x_107_, v_b_94_);
v___x_109_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_95_, v___x_108_, v_k_96_);
lean_dec_ref(v___x_108_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0___boxed(lean_object* v_altsUsed_111_, lean_object* v_j_112_, lean_object* v_fvar_113_, lean_object* v_b_114_, lean_object* v___x_115_, lean_object* v_k_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
uint8_t v___x_2541__boxed_122_; lean_object* v_res_123_; 
v___x_2541__boxed_122_ = lean_unbox(v___x_115_);
v_res_123_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0(v_altsUsed_111_, v_j_112_, v_fvar_113_, v_b_114_, v___x_2541__boxed_122_, v_k_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v_fvar_113_);
lean_dec(v_j_112_);
lean_dec_ref(v_altsUsed_111_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(lean_object* v_altsUsed_124_, lean_object* v_fvar_125_, lean_object* v_b_126_, lean_object* v_as_127_, lean_object* v_i_128_, lean_object* v_j_129_, lean_object* v_bs_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_zero_136_; uint8_t v_isZero_137_; 
v_zero_136_ = lean_unsigned_to_nat(0u);
v_isZero_137_ = lean_nat_dec_eq(v_i_128_, v_zero_136_);
if (v_isZero_137_ == 1)
{
lean_object* v___x_138_; 
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v_j_129_);
lean_dec(v_i_128_);
lean_dec_ref(v_b_126_);
lean_dec(v_fvar_125_);
lean_dec_ref(v_altsUsed_124_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v_bs_130_);
return v___x_138_;
}
else
{
uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_139_ = 1;
v___x_140_ = lean_box(v___x_139_);
lean_inc_ref(v_b_126_);
lean_inc(v_fvar_125_);
lean_inc(v_j_129_);
lean_inc_ref(v_altsUsed_124_);
v___f_141_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_141_, 0, v_altsUsed_124_);
lean_closure_set(v___f_141_, 1, v_j_129_);
lean_closure_set(v___f_141_, 2, v_fvar_125_);
lean_closure_set(v___f_141_, 3, v_b_126_);
lean_closure_set(v___f_141_, 4, v___x_140_);
v___x_142_ = lean_array_fget_borrowed(v_as_127_, v_j_129_);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___x_142_);
v___x_143_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v___x_142_, v___f_141_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v_one_145_; lean_object* v_n_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_a_144_);
lean_dec_ref(v___x_143_);
v_one_145_ = lean_unsigned_to_nat(1u);
v_n_146_ = lean_nat_sub(v_i_128_, v_one_145_);
lean_dec(v_i_128_);
v___x_147_ = lean_nat_add(v_j_129_, v_one_145_);
lean_dec(v_j_129_);
v___x_148_ = lean_array_push(v_bs_130_, v_a_144_);
v_i_128_ = v_n_146_;
v_j_129_ = v___x_147_;
v_bs_130_ = v___x_148_;
goto _start;
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec_ref(v_bs_130_);
lean_dec(v_j_129_);
lean_dec(v_i_128_);
lean_dec_ref(v_b_126_);
lean_dec(v_fvar_125_);
lean_dec_ref(v_altsUsed_124_);
v_a_150_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_143_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_143_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___boxed(lean_object* v_altsUsed_158_, lean_object* v_fvar_159_, lean_object* v_b_160_, lean_object* v_as_161_, lean_object* v_i_162_, lean_object* v_j_163_, lean_object* v_bs_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_158_, v_fvar_159_, v_b_160_, v_as_161_, v_i_162_, v_j_163_, v_bs_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec_ref(v_as_161_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(lean_object* v_fvar_171_, lean_object* v_b_172_, size_t v_sz_173_, size_t v_i_174_, lean_object* v_bs_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = lean_usize_dec_lt(v_i_174_, v_sz_173_);
if (v___x_176_ == 0)
{
lean_dec_ref(v_b_172_);
return v_bs_175_;
}
else
{
lean_object* v_v_177_; lean_object* v___x_178_; lean_object* v_bs_x27_179_; lean_object* v___y_181_; uint8_t v___x_186_; 
v_v_177_ = lean_array_uget(v_bs_175_, v_i_174_);
v___x_178_ = lean_unsigned_to_nat(0u);
v_bs_x27_179_ = lean_array_uset(v_bs_175_, v_i_174_, v___x_178_);
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_v_177_, v_fvar_171_);
if (v___x_186_ == 0)
{
v___y_181_ = v_v_177_;
goto v___jp_180_;
}
else
{
uint8_t v___x_187_; lean_object* v___x_188_; 
v___x_187_ = 1;
lean_inc_ref(v_b_172_);
v___x_188_ = l_Lean_Compiler_LCNF_CodeDecl_collectUsed(v___x_187_, v_b_172_, v_v_177_);
v___y_181_ = v___x_188_;
goto v___jp_180_;
}
v___jp_180_:
{
size_t v___x_182_; size_t v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((size_t)1ULL);
v___x_183_ = lean_usize_add(v_i_174_, v___x_182_);
v___x_184_ = lean_array_uset(v_bs_x27_179_, v_i_174_, v___y_181_);
v_i_174_ = v___x_183_;
v_bs_175_ = v___x_184_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3___boxed(lean_object* v_fvar_189_, lean_object* v_b_190_, lean_object* v_sz_191_, lean_object* v_i_192_, lean_object* v_bs_193_){
_start:
{
size_t v_sz_boxed_194_; size_t v_i_boxed_195_; lean_object* v_res_196_; 
v_sz_boxed_194_ = lean_unbox_usize(v_sz_191_);
lean_dec(v_sz_191_);
v_i_boxed_195_ = lean_unbox_usize(v_i_192_);
lean_dec(v_i_192_);
v_res_196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(v_fvar_189_, v_b_190_, v_sz_boxed_194_, v_i_boxed_195_, v_bs_193_);
lean_dec(v_fvar_189_);
return v_res_196_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0(void){
_start:
{
uint8_t v___x_197_; lean_object* v___x_198_; 
v___x_197_ = 1;
v___x_198_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(lean_object* v_decls_199_, lean_object* v_alts_200_, lean_object* v_altsUsed_201_, lean_object* v_ctx_202_, lean_object* v_ctxUsed_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_209_ = lean_array_get_size(v_decls_199_);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_nat_dec_eq(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_b_216_; lean_object* v_bs_217_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_212_ = 1;
v___x_213_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0);
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_sub(v___x_209_, v___x_214_);
v_b_216_ = lean_array_get(v___x_213_, v_decls_199_, v___x_215_);
lean_dec(v___x_215_);
v_bs_217_ = lean_array_pop(v_decls_199_);
lean_inc(v_b_216_);
lean_inc_ref(v_bs_217_);
v___x_240_ = lean_array_push(v_bs_217_, v_b_216_);
lean_inc_ref(v_ctx_202_);
v___x_241_ = l_Array_reverse___redArg(v_ctx_202_);
v___x_242_ = l_Array_append___redArg(v___x_240_, v___x_241_);
lean_dec_ref(v___x_241_);
lean_inc_ref(v_alts_200_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v_alts_200_);
if (lean_obj_tag(v_b_216_) == 0)
{
lean_object* v_decl_244_; lean_object* v_fvarId_245_; lean_object* v_value_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; 
v_decl_244_ = lean_ctor_get(v_b_216_, 0);
v_fvarId_245_ = lean_ctor_get(v_decl_244_, 0);
v_value_246_ = lean_ctor_get(v_decl_244_, 3);
lean_inc_ref(v_b_216_);
lean_inc_ref(v_ctx_202_);
v___x_247_ = lean_array_push(v_ctx_202_, v_b_216_);
lean_inc_ref(v_ctxUsed_203_);
lean_inc_ref(v_b_216_);
v___x_248_ = l_Lean_Compiler_LCNF_CodeDecl_collectUsed(v___x_212_, v_b_216_, v_ctxUsed_203_);
switch(lean_obj_tag(v_value_246_))
{
case 7:
{
lean_dec_ref(v___x_243_);
v___y_250_ = v_a_204_;
v___y_251_ = v_a_205_;
v___y_252_ = v_a_206_;
v___y_253_ = v_a_207_;
goto v___jp_249_;
}
case 6:
{
lean_dec_ref(v___x_243_);
v___y_250_ = v_a_204_;
v___y_251_ = v_a_205_;
v___y_252_ = v_a_206_;
v___y_253_ = v_a_207_;
goto v___jp_249_;
}
case 8:
{
lean_dec_ref(v___x_243_);
v___y_250_ = v_a_204_;
v___y_251_ = v_a_205_;
v___y_252_ = v_a_206_;
v___y_253_ = v_a_207_;
goto v___jp_249_;
}
default: 
{
lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref(v___x_248_);
lean_dec_ref(v___x_247_);
lean_dec_ref(v_bs_217_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec_ref(v_ctxUsed_203_);
lean_dec_ref(v_ctx_202_);
lean_dec_ref(v_altsUsed_201_);
lean_dec_ref(v_alts_200_);
v_isSharedCheck_262_ = !lean_is_exclusive(v_b_216_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v_b_216_, 0);
lean_dec(v_unused_263_);
v___x_257_ = v_b_216_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_dec(v_b_216_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_243_);
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_243_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
v___jp_249_:
{
uint8_t v___x_254_; 
v___x_254_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_ctxUsed_203_, v_fvarId_245_);
if (v___x_254_ == 0)
{
lean_dec_ref(v___x_248_);
lean_dec_ref(v___x_247_);
lean_inc(v_fvarId_245_);
v___y_219_ = v___y_251_;
v___y_220_ = v___y_252_;
v___y_221_ = v___y_253_;
v___y_222_ = v_fvarId_245_;
v___y_223_ = v___y_250_;
goto v___jp_218_;
}
else
{
if (v___x_211_ == 0)
{
lean_dec_ref(v_b_216_);
lean_dec_ref(v_ctxUsed_203_);
lean_dec_ref(v_ctx_202_);
v_decls_199_ = v_bs_217_;
v_ctx_202_ = v___x_247_;
v_ctxUsed_203_ = v___x_248_;
v_a_204_ = v___y_250_;
v_a_205_ = v___y_251_;
v_a_206_ = v___y_252_;
v_a_207_ = v___y_253_;
goto _start;
}
else
{
lean_dec_ref(v___x_248_);
lean_dec_ref(v___x_247_);
lean_inc(v_fvarId_245_);
v___y_219_ = v___y_251_;
v___y_220_ = v___y_252_;
v___y_221_ = v___y_253_;
v___y_222_ = v_fvarId_245_;
v___y_223_ = v___y_250_;
goto v___jp_218_;
}
}
}
}
else
{
lean_object* v___x_264_; 
lean_dec_ref(v_bs_217_);
lean_dec(v_b_216_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec_ref(v_ctxUsed_203_);
lean_dec_ref(v_ctx_202_);
lean_dec_ref(v_altsUsed_201_);
lean_dec_ref(v_alts_200_);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_243_);
return v___x_264_;
}
v___jp_218_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_array_get_size(v_alts_200_);
v___x_225_ = lean_mk_empty_array_with_capacity(v___x_224_);
lean_inc(v___y_221_);
lean_inc_ref(v___y_220_);
lean_inc(v___y_219_);
lean_inc_ref(v___y_223_);
lean_inc(v_b_216_);
lean_inc(v___y_222_);
lean_inc_ref(v_altsUsed_201_);
v___x_226_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_201_, v___y_222_, v_b_216_, v_alts_200_, v___x_224_, v___x_210_, v___x_225_, v___y_223_, v___y_219_, v___y_220_, v___y_221_);
lean_dec_ref(v_alts_200_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; size_t v_sz_228_; size_t v___x_229_; lean_object* v___x_230_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref(v___x_226_);
v_sz_228_ = lean_array_size(v_altsUsed_201_);
v___x_229_ = ((size_t)0ULL);
v___x_230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(v___y_222_, v_b_216_, v_sz_228_, v___x_229_, v_altsUsed_201_);
lean_dec(v___y_222_);
v_decls_199_ = v_bs_217_;
v_alts_200_ = v_a_227_;
v_altsUsed_201_ = v___x_230_;
v_a_204_ = v___y_223_;
v_a_205_ = v___y_219_;
v_a_206_ = v___y_220_;
v_a_207_ = v___y_221_;
goto _start;
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v_bs_217_);
lean_dec(v_b_216_);
lean_dec_ref(v_ctxUsed_203_);
lean_dec_ref(v_ctx_202_);
lean_dec_ref(v_altsUsed_201_);
v_a_232_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_226_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_226_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec_ref(v_ctxUsed_203_);
lean_dec_ref(v_altsUsed_201_);
lean_dec_ref(v_decls_199_);
v___x_265_ = l_Array_reverse___redArg(v_ctx_202_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v_alts_200_);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___boxed(lean_object* v_decls_268_, lean_object* v_alts_269_, lean_object* v_altsUsed_270_, lean_object* v_ctx_271_, lean_object* v_ctxUsed_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(v_decls_268_, v_alts_269_, v_altsUsed_270_, v_ctx_271_, v_ctxUsed_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
return v_res_278_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0(lean_object* v_00_u03b2_279_, lean_object* v_m_280_, lean_object* v_a_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_m_280_, v_a_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___boxed(lean_object* v_00_u03b2_283_, lean_object* v_m_284_, lean_object* v_a_285_){
_start:
{
uint8_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0(v_00_u03b2_283_, v_m_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_m_284_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2(lean_object* v_altsUsed_288_, lean_object* v_fvar_289_, lean_object* v_b_290_, lean_object* v_as_291_, lean_object* v_i_292_, lean_object* v_j_293_, lean_object* v_inv_294_, lean_object* v_bs_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_288_, v_fvar_289_, v_b_290_, v_as_291_, v_i_292_, v_j_293_, v_bs_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___boxed(lean_object* v_altsUsed_302_, lean_object* v_fvar_303_, lean_object* v_b_304_, lean_object* v_as_305_, lean_object* v_i_306_, lean_object* v_j_307_, lean_object* v_inv_308_, lean_object* v_bs_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2(v_altsUsed_302_, v_fvar_303_, v_b_304_, v_as_305_, v_i_306_, v_j_307_, v_inv_308_, v_bs_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec_ref(v_as_305_);
return v_res_315_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0(lean_object* v_00_u03b2_316_, lean_object* v_a_317_, lean_object* v_x_318_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_317_, v_x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_320_, lean_object* v_a_321_, lean_object* v_x_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0(v_00_u03b2_320_, v_a_321_, v_x_322_);
lean_dec(v_x_322_);
lean_dec(v_a_321_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(size_t v_sz_325_, size_t v_i_326_, lean_object* v_bs_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_usize_dec_lt(v_i_326_, v_sz_325_);
if (v___x_328_ == 0)
{
return v_bs_327_;
}
else
{
lean_object* v___x_329_; lean_object* v_v_330_; lean_object* v___x_331_; lean_object* v_bs_x27_332_; uint8_t v___x_333_; lean_object* v___y_335_; 
v___x_329_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v_v_330_ = lean_array_uget(v_bs_327_, v_i_326_);
v___x_331_ = lean_unsigned_to_nat(0u);
v_bs_x27_332_ = lean_array_uset(v_bs_327_, v_i_326_, v___x_331_);
v___x_333_ = 1;
switch(lean_obj_tag(v_v_330_))
{
case 0:
{
lean_object* v_code_341_; 
v_code_341_ = lean_ctor_get(v_v_330_, 2);
lean_inc_ref(v_code_341_);
lean_dec_ref(v_v_330_);
v___y_335_ = v_code_341_;
goto v___jp_334_;
}
case 1:
{
lean_object* v_code_342_; 
v_code_342_ = lean_ctor_get(v_v_330_, 1);
lean_inc_ref(v_code_342_);
lean_dec_ref(v_v_330_);
v___y_335_ = v_code_342_;
goto v___jp_334_;
}
default: 
{
lean_object* v_code_343_; 
v_code_343_ = lean_ctor_get(v_v_330_, 0);
lean_inc_ref(v_code_343_);
lean_dec_ref(v_v_330_);
v___y_335_ = v_code_343_;
goto v___jp_334_;
}
}
v___jp_334_:
{
lean_object* v___x_336_; size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v___x_336_ = l_Lean_Compiler_LCNF_Code_collectUsed(v___x_333_, v___y_335_, v___x_329_);
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_add(v_i_326_, v___x_337_);
v___x_339_ = lean_array_uset(v_bs_x27_332_, v_i_326_, v___x_336_);
v_i_326_ = v___x_338_;
v_bs_327_ = v___x_339_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1___boxed(lean_object* v_sz_344_, lean_object* v_i_345_, lean_object* v_bs_346_){
_start:
{
size_t v_sz_boxed_347_; size_t v_i_boxed_348_; lean_object* v_res_349_; 
v_sz_boxed_347_ = lean_unbox_usize(v_sz_344_);
lean_dec(v_sz_344_);
v_i_boxed_348_ = lean_unbox_usize(v_i_345_);
lean_dec(v_i_345_);
v_res_349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(v_sz_boxed_347_, v_i_boxed_348_, v_bs_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
return v_x_350_;
}
else
{
lean_object* v_key_352_; lean_object* v_value_353_; lean_object* v_tail_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_377_; 
v_key_352_ = lean_ctor_get(v_x_351_, 0);
v_value_353_ = lean_ctor_get(v_x_351_, 1);
v_tail_354_ = lean_ctor_get(v_x_351_, 2);
v_isSharedCheck_377_ = !lean_is_exclusive(v_x_351_);
if (v_isSharedCheck_377_ == 0)
{
v___x_356_ = v_x_351_;
v_isShared_357_ = v_isSharedCheck_377_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_tail_354_);
lean_inc(v_value_353_);
lean_inc(v_key_352_);
lean_dec(v_x_351_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_377_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; uint64_t v___x_359_; uint64_t v___x_360_; uint64_t v___x_361_; uint64_t v_fold_362_; uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v___x_365_; size_t v___x_366_; size_t v___x_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_358_ = lean_array_get_size(v_x_350_);
v___x_359_ = l_Lean_instHashableFVarId_hash(v_key_352_);
v___x_360_ = 32ULL;
v___x_361_ = lean_uint64_shift_right(v___x_359_, v___x_360_);
v_fold_362_ = lean_uint64_xor(v___x_359_, v___x_361_);
v___x_363_ = 16ULL;
v___x_364_ = lean_uint64_shift_right(v_fold_362_, v___x_363_);
v___x_365_ = lean_uint64_xor(v_fold_362_, v___x_364_);
v___x_366_ = lean_uint64_to_usize(v___x_365_);
v___x_367_ = lean_usize_of_nat(v___x_358_);
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_sub(v___x_367_, v___x_368_);
v___x_370_ = lean_usize_land(v___x_366_, v___x_369_);
v___x_371_ = lean_array_uget_borrowed(v_x_350_, v___x_370_);
lean_inc(v___x_371_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 2, v___x_371_);
v___x_373_ = v___x_356_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_key_352_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_value_353_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v___x_371_);
v___x_373_ = v_reuseFailAlloc_376_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; 
v___x_374_ = lean_array_uset(v_x_350_, v___x_370_, v___x_373_);
v_x_350_ = v___x_374_;
v_x_351_ = v_tail_354_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4___redArg(lean_object* v_i_378_, lean_object* v_source_379_, lean_object* v_target_380_){
_start:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_array_get_size(v_source_379_);
v___x_382_ = lean_nat_dec_lt(v_i_378_, v___x_381_);
if (v___x_382_ == 0)
{
lean_dec_ref(v_source_379_);
lean_dec(v_i_378_);
return v_target_380_;
}
else
{
lean_object* v_es_383_; lean_object* v___x_384_; lean_object* v_source_385_; lean_object* v_target_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_es_383_ = lean_array_fget(v_source_379_, v_i_378_);
v___x_384_ = lean_box(0);
v_source_385_ = lean_array_fset(v_source_379_, v_i_378_, v___x_384_);
v_target_386_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6___redArg(v_target_380_, v_es_383_);
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = lean_nat_add(v_i_378_, v___x_387_);
lean_dec(v_i_378_);
v_i_378_ = v___x_388_;
v_source_379_ = v_source_385_;
v_target_380_ = v_target_386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3___redArg(lean_object* v_data_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_nbuckets_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_391_ = lean_array_get_size(v_data_390_);
v___x_392_ = lean_unsigned_to_nat(2u);
v_nbuckets_393_ = lean_nat_mul(v___x_391_, v___x_392_);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_box(0);
v___x_396_ = lean_mk_array(v_nbuckets_393_, v___x_395_);
v___x_397_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4___redArg(v___x_394_, v_data_390_, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___redArg(lean_object* v_m_398_, lean_object* v_a_399_, lean_object* v_b_400_){
_start:
{
lean_object* v_size_401_; lean_object* v_buckets_402_; lean_object* v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v___x_406_; uint64_t v_fold_407_; uint64_t v___x_408_; uint64_t v___x_409_; uint64_t v___x_410_; size_t v___x_411_; size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; size_t v___x_415_; lean_object* v_bkt_416_; uint8_t v___x_417_; 
v_size_401_ = lean_ctor_get(v_m_398_, 0);
v_buckets_402_ = lean_ctor_get(v_m_398_, 1);
v___x_403_ = lean_array_get_size(v_buckets_402_);
v___x_404_ = l_Lean_instHashableFVarId_hash(v_a_399_);
v___x_405_ = 32ULL;
v___x_406_ = lean_uint64_shift_right(v___x_404_, v___x_405_);
v_fold_407_ = lean_uint64_xor(v___x_404_, v___x_406_);
v___x_408_ = 16ULL;
v___x_409_ = lean_uint64_shift_right(v_fold_407_, v___x_408_);
v___x_410_ = lean_uint64_xor(v_fold_407_, v___x_409_);
v___x_411_ = lean_uint64_to_usize(v___x_410_);
v___x_412_ = lean_usize_of_nat(v___x_403_);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_sub(v___x_412_, v___x_413_);
v___x_415_ = lean_usize_land(v___x_411_, v___x_414_);
v_bkt_416_ = lean_array_uget_borrowed(v_buckets_402_, v___x_415_);
v___x_417_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_399_, v_bkt_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_438_; 
lean_inc_ref(v_buckets_402_);
lean_inc(v_size_401_);
v_isSharedCheck_438_ = !lean_is_exclusive(v_m_398_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; lean_object* v_unused_440_; 
v_unused_439_ = lean_ctor_get(v_m_398_, 1);
lean_dec(v_unused_439_);
v_unused_440_ = lean_ctor_get(v_m_398_, 0);
lean_dec(v_unused_440_);
v___x_419_ = v_m_398_;
v_isShared_420_ = v_isSharedCheck_438_;
goto v_resetjp_418_;
}
else
{
lean_dec(v_m_398_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_438_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v_size_x27_422_; lean_object* v___x_423_; lean_object* v_buckets_x27_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v_size_x27_422_ = lean_nat_add(v_size_401_, v___x_421_);
lean_dec(v_size_401_);
lean_inc(v_bkt_416_);
v___x_423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_423_, 0, v_a_399_);
lean_ctor_set(v___x_423_, 1, v_b_400_);
lean_ctor_set(v___x_423_, 2, v_bkt_416_);
v_buckets_x27_424_ = lean_array_uset(v_buckets_402_, v___x_415_, v___x_423_);
v___x_425_ = lean_unsigned_to_nat(4u);
v___x_426_ = lean_nat_mul(v_size_x27_422_, v___x_425_);
v___x_427_ = lean_unsigned_to_nat(3u);
v___x_428_ = lean_nat_div(v___x_426_, v___x_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_array_get_size(v_buckets_x27_424_);
v___x_430_ = lean_nat_dec_le(v___x_428_, v___x_429_);
lean_dec(v___x_428_);
if (v___x_430_ == 0)
{
lean_object* v_val_431_; lean_object* v___x_433_; 
v_val_431_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3___redArg(v_buckets_x27_424_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v_val_431_);
lean_ctor_set(v___x_419_, 0, v_size_x27_422_);
v___x_433_ = v___x_419_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_size_x27_422_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_val_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
else
{
lean_object* v___x_436_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v_buckets_x27_424_);
lean_ctor_set(v___x_419_, 0, v_size_x27_422_);
v___x_436_ = v___x_419_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_size_x27_422_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_buckets_x27_424_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
else
{
lean_dec(v_b_400_);
lean_dec(v_a_399_);
return v_m_398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed(lean_object* v_code_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(v_code_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(lean_object* v_i_450_, lean_object* v_as_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_array_get_size(v_as_451_);
v___x_458_ = lean_nat_dec_lt(v_i_450_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v_i_450_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v_as_451_);
return v___x_459_;
}
else
{
lean_object* v_a_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_a_460_ = lean_array_fget_borrowed(v_as_451_, v_i_450_);
v___x_461_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed), 6, 0);
lean_inc(v___y_455_);
lean_inc_ref(v___y_454_);
lean_inc(v___y_453_);
lean_inc_ref(v___y_452_);
lean_inc(v_a_460_);
v___x_462_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v_a_460_, v___x_461_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; size_t v___x_464_; size_t v___x_465_; uint8_t v___x_466_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref(v___x_462_);
v___x_464_ = lean_ptr_addr(v_a_460_);
v___x_465_ = lean_ptr_addr(v_a_463_);
v___x_466_ = lean_usize_dec_eq(v___x_464_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = lean_nat_add(v_i_450_, v___x_467_);
v___x_469_ = lean_array_fset(v_as_451_, v_i_450_, v_a_463_);
lean_dec(v_i_450_);
v_i_450_ = v___x_468_;
v_as_451_ = v___x_469_;
goto _start;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec(v_a_463_);
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_nat_add(v_i_450_, v___x_471_);
lean_dec(v_i_450_);
v_i_450_ = v___x_472_;
goto _start;
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec_ref(v_as_451_);
lean_dec(v_i_450_);
v_a_474_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_462_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_462_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(lean_object* v_c_482_, lean_object* v_decls_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_typeName_489_; lean_object* v_resultType_490_; lean_object* v_discr_491_; lean_object* v_alts_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_539_; 
v_typeName_489_ = lean_ctor_get(v_c_482_, 0);
v_resultType_490_ = lean_ctor_get(v_c_482_, 1);
v_discr_491_ = lean_ctor_get(v_c_482_, 2);
v_alts_492_ = lean_ctor_get(v_c_482_, 3);
v_isSharedCheck_539_ = !lean_is_exclusive(v_c_482_);
if (v_isSharedCheck_539_ == 0)
{
v___x_494_ = v_c_482_;
v_isShared_495_ = v_isSharedCheck_539_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_alts_492_);
lean_inc(v_discr_491_);
lean_inc(v_resultType_490_);
lean_inc(v_typeName_489_);
lean_dec(v_c_482_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_539_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; size_t v_sz_497_; size_t v___x_498_; lean_object* v_altsUsed_499_; lean_object* v___x_500_; lean_object* v_ctxUsed_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_496_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v_sz_497_ = lean_array_size(v_alts_492_);
v___x_498_ = ((size_t)0ULL);
lean_inc_ref(v_alts_492_);
v_altsUsed_499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(v_sz_497_, v___x_498_, v_alts_492_);
v___x_500_ = lean_box(0);
lean_inc(v_discr_491_);
v_ctxUsed_501_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___redArg(v___x_496_, v_discr_491_, v___x_500_);
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0));
lean_inc(v_a_487_);
lean_inc_ref(v_a_486_);
lean_inc(v_a_485_);
lean_inc_ref(v_a_484_);
v___x_504_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(v_decls_483_, v_alts_492_, v_altsUsed_499_, v___x_503_, v_ctxUsed_501_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_508_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref(v___x_504_);
v_fst_506_ = lean_ctor_get(v_a_505_, 0);
lean_inc(v_fst_506_);
v_snd_507_ = lean_ctor_get(v_a_505_, 1);
lean_inc(v_snd_507_);
lean_dec(v_a_505_);
v___x_508_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(v___x_502_, v_snd_507_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_522_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_522_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_522_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_522_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
uint8_t v___x_513_; lean_object* v___x_515_; 
v___x_513_ = 1;
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 3, v_a_509_);
v___x_515_ = v___x_494_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_typeName_489_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_resultType_490_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_discr_491_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v_a_509_);
v___x_515_ = v_reuseFailAlloc_521_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_516_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
v___x_517_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_513_, v_fst_506_, v___x_516_);
lean_dec(v_fst_506_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_517_);
v___x_519_ = v___x_511_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_fst_506_);
lean_del_object(v___x_494_);
lean_dec(v_discr_491_);
lean_dec_ref(v_resultType_490_);
lean_dec(v_typeName_489_);
v_a_523_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_508_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_508_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_del_object(v___x_494_);
lean_dec(v_discr_491_);
lean_dec_ref(v_resultType_490_);
lean_dec(v_typeName_489_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
v_a_531_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_504_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_504_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(lean_object* v_c_540_, lean_object* v_decls_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
switch(lean_obj_tag(v_c_540_))
{
case 0:
{
lean_object* v_decl_547_; lean_object* v_k_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_decl_547_ = lean_ctor_get(v_c_540_, 0);
lean_inc_ref(v_decl_547_);
v_k_548_ = lean_ctor_get(v_c_540_, 1);
lean_inc_ref(v_k_548_);
lean_dec_ref(v_c_540_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v_decl_547_);
v___x_550_ = lean_array_push(v_decls_541_, v___x_549_);
v_c_540_ = v_k_548_;
v_decls_541_ = v___x_550_;
goto _start;
}
case 2:
{
lean_object* v_decl_552_; lean_object* v_k_553_; lean_object* v_params_554_; lean_object* v_type_555_; lean_object* v_value_556_; lean_object* v___x_557_; 
v_decl_552_ = lean_ctor_get(v_c_540_, 0);
lean_inc_ref(v_decl_552_);
v_k_553_ = lean_ctor_get(v_c_540_, 1);
lean_inc_ref(v_k_553_);
lean_dec_ref(v_c_540_);
v_params_554_ = lean_ctor_get(v_decl_552_, 2);
lean_inc_ref(v_params_554_);
v_type_555_ = lean_ctor_get(v_decl_552_, 3);
lean_inc_ref(v_type_555_);
v_value_556_ = lean_ctor_get(v_decl_552_, 4);
lean_inc(v_a_545_);
lean_inc_ref(v_a_544_);
lean_inc(v_a_543_);
lean_inc_ref(v_a_542_);
lean_inc_ref(v_value_556_);
v___x_557_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(v_value_556_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_578_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_578_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_578_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_578_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
uint8_t v___x_562_; lean_object* v___x_563_; 
v___x_562_ = 1;
v___x_563_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_562_, v_decl_552_, v_type_555_, v_params_554_, v_a_558_, v_a_543_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref(v___x_563_);
if (v_isShared_561_ == 0)
{
lean_ctor_set_tag(v___x_560_, 2);
lean_ctor_set(v___x_560_, 0, v_a_564_);
v___x_566_ = v___x_560_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_564_);
v___x_566_ = v_reuseFailAlloc_569_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; 
v___x_567_ = lean_array_push(v_decls_541_, v___x_566_);
v_c_540_ = v_k_553_;
v_decls_541_ = v___x_567_;
goto _start;
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_del_object(v___x_560_);
lean_dec_ref(v_k_553_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec_ref(v_decls_541_);
v_a_570_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_563_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_563_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_555_);
lean_dec_ref(v_params_554_);
lean_dec_ref(v_k_553_);
lean_dec_ref(v_decl_552_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec_ref(v_decls_541_);
return v___x_557_;
}
}
case 4:
{
lean_object* v_cases_579_; lean_object* v___x_580_; 
v_cases_579_ = lean_ctor_get(v_c_540_, 0);
lean_inc_ref(v_cases_579_);
lean_dec_ref(v_c_540_);
v___x_580_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(v_cases_579_, v_decls_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
return v___x_580_;
}
case 7:
{
lean_object* v_fvarId_581_; lean_object* v_i_582_; lean_object* v_y_583_; lean_object* v_k_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_fvarId_581_ = lean_ctor_get(v_c_540_, 0);
lean_inc(v_fvarId_581_);
v_i_582_ = lean_ctor_get(v_c_540_, 1);
lean_inc(v_i_582_);
v_y_583_ = lean_ctor_get(v_c_540_, 2);
lean_inc(v_y_583_);
v_k_584_ = lean_ctor_get(v_c_540_, 3);
lean_inc_ref(v_k_584_);
lean_dec_ref(v_c_540_);
v___x_585_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_585_, 0, v_fvarId_581_);
lean_ctor_set(v___x_585_, 1, v_i_582_);
lean_ctor_set(v___x_585_, 2, v_y_583_);
v___x_586_ = lean_array_push(v_decls_541_, v___x_585_);
v_c_540_ = v_k_584_;
v_decls_541_ = v___x_586_;
goto _start;
}
case 8:
{
lean_object* v_fvarId_588_; lean_object* v_i_589_; lean_object* v_y_590_; lean_object* v_k_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_fvarId_588_ = lean_ctor_get(v_c_540_, 0);
lean_inc(v_fvarId_588_);
v_i_589_ = lean_ctor_get(v_c_540_, 1);
lean_inc(v_i_589_);
v_y_590_ = lean_ctor_get(v_c_540_, 2);
lean_inc(v_y_590_);
v_k_591_ = lean_ctor_get(v_c_540_, 3);
lean_inc_ref(v_k_591_);
lean_dec_ref(v_c_540_);
v___x_592_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_592_, 0, v_fvarId_588_);
lean_ctor_set(v___x_592_, 1, v_i_589_);
lean_ctor_set(v___x_592_, 2, v_y_590_);
v___x_593_ = lean_array_push(v_decls_541_, v___x_592_);
v_c_540_ = v_k_591_;
v_decls_541_ = v___x_593_;
goto _start;
}
case 9:
{
lean_object* v_fvarId_595_; lean_object* v_i_596_; lean_object* v_offset_597_; lean_object* v_y_598_; lean_object* v_ty_599_; lean_object* v_k_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_fvarId_595_ = lean_ctor_get(v_c_540_, 0);
lean_inc(v_fvarId_595_);
v_i_596_ = lean_ctor_get(v_c_540_, 1);
lean_inc(v_i_596_);
v_offset_597_ = lean_ctor_get(v_c_540_, 2);
lean_inc(v_offset_597_);
v_y_598_ = lean_ctor_get(v_c_540_, 3);
lean_inc(v_y_598_);
v_ty_599_ = lean_ctor_get(v_c_540_, 4);
lean_inc_ref(v_ty_599_);
v_k_600_ = lean_ctor_get(v_c_540_, 5);
lean_inc_ref(v_k_600_);
lean_dec_ref(v_c_540_);
v___x_601_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v___x_601_, 0, v_fvarId_595_);
lean_ctor_set(v___x_601_, 1, v_i_596_);
lean_ctor_set(v___x_601_, 2, v_offset_597_);
lean_ctor_set(v___x_601_, 3, v_y_598_);
lean_ctor_set(v___x_601_, 4, v_ty_599_);
v___x_602_ = lean_array_push(v_decls_541_, v___x_601_);
v_c_540_ = v_k_600_;
v_decls_541_ = v___x_602_;
goto _start;
}
case 10:
{
lean_object* v_fvarId_604_; lean_object* v_cidx_605_; lean_object* v_k_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_fvarId_604_ = lean_ctor_get(v_c_540_, 0);
lean_inc(v_fvarId_604_);
v_cidx_605_ = lean_ctor_get(v_c_540_, 1);
lean_inc(v_cidx_605_);
v_k_606_ = lean_ctor_get(v_c_540_, 2);
lean_inc_ref(v_k_606_);
lean_dec_ref(v_c_540_);
v___x_607_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_607_, 0, v_fvarId_604_);
lean_ctor_set(v___x_607_, 1, v_cidx_605_);
v___x_608_ = lean_array_push(v_decls_541_, v___x_607_);
v_c_540_ = v_k_606_;
v_decls_541_ = v___x_608_;
goto _start;
}
case 11:
{
lean_object* v_fvarId_610_; lean_object* v_n_611_; uint8_t v_check_612_; uint8_t v_persistent_613_; lean_object* v_k_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_fvarId_610_ = lean_ctor_get(v_c_540_, 0);
lean_inc(v_fvarId_610_);
v_n_611_ = lean_ctor_get(v_c_540_, 1);
lean_inc(v_n_611_);
v_check_612_ = lean_ctor_get_uint8(v_c_540_, sizeof(void*)*3);
v_persistent_613_ = lean_ctor_get_uint8(v_c_540_, sizeof(void*)*3 + 1);
v_k_614_ = lean_ctor_get(v_c_540_, 2);
lean_inc_ref(v_k_614_);
lean_dec_ref(v_c_540_);
v___x_615_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v___x_615_, 0, v_fvarId_610_);
lean_ctor_set(v___x_615_, 1, v_n_611_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*2, v_check_612_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*2 + 1, v_persistent_613_);
v___x_616_ = lean_array_push(v_decls_541_, v___x_615_);
v_c_540_ = v_k_614_;
v_decls_541_ = v___x_616_;
goto _start;
}
case 12:
{
lean_object* v_fvarId_618_; lean_object* v_n_619_; uint8_t v_check_620_; uint8_t v_persistent_621_; lean_object* v_k_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_fvarId_618_ = lean_ctor_get(v_c_540_, 0);
lean_inc(v_fvarId_618_);
v_n_619_ = lean_ctor_get(v_c_540_, 1);
lean_inc(v_n_619_);
v_check_620_ = lean_ctor_get_uint8(v_c_540_, sizeof(void*)*3);
v_persistent_621_ = lean_ctor_get_uint8(v_c_540_, sizeof(void*)*3 + 1);
v_k_622_ = lean_ctor_get(v_c_540_, 2);
lean_inc_ref(v_k_622_);
lean_dec_ref(v_c_540_);
v___x_623_ = lean_alloc_ctor(8, 2, 2);
lean_ctor_set(v___x_623_, 0, v_fvarId_618_);
lean_ctor_set(v___x_623_, 1, v_n_619_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*2, v_check_620_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*2 + 1, v_persistent_621_);
v___x_624_ = lean_array_push(v_decls_541_, v___x_623_);
v_c_540_ = v_k_622_;
v_decls_541_ = v___x_624_;
goto _start;
}
case 13:
{
lean_object* v_fvarId_626_; lean_object* v_k_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_fvarId_626_ = lean_ctor_get(v_c_540_, 0);
lean_inc(v_fvarId_626_);
v_k_627_ = lean_ctor_get(v_c_540_, 1);
lean_inc_ref(v_k_627_);
lean_dec_ref(v_c_540_);
v___x_628_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_628_, 0, v_fvarId_626_);
v___x_629_ = lean_array_push(v_decls_541_, v___x_628_);
v_c_540_ = v_k_627_;
v_decls_541_ = v___x_629_;
goto _start;
}
default: 
{
uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
v___x_631_ = 1;
v___x_632_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_631_, v_decls_541_, v_c_540_);
lean_dec_ref(v_decls_541_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(lean_object* v_code_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0));
v___x_641_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(v_code_634_, v___x_640_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___boxed(lean_object* v_i_642_, lean_object* v_as_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(v_i_642_, v_as_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___boxed(lean_object* v_c_650_, lean_object* v_decls_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(v_c_650_, v_decls_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go___boxed(lean_object* v_c_658_, lean_object* v_decls_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(v_c_658_, v_decls_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2(lean_object* v_00_u03b2_666_, lean_object* v_m_667_, lean_object* v_a_668_, lean_object* v_b_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___redArg(v_m_667_, v_a_668_, v_b_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3(lean_object* v_00_u03b2_671_, lean_object* v_data_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3___redArg(v_data_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_674_, lean_object* v_i_675_, lean_object* v_source_676_, lean_object* v_target_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4___redArg(v_i_675_, v_source_676_, v_target_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_679_, lean_object* v_x_680_, lean_object* v_x_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6___redArg(v_x_680_, v_x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(lean_object* v_f_683_, lean_object* v_v_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
if (lean_obj_tag(v_v_684_) == 0)
{
lean_object* v_code_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_714_; 
v_code_690_ = lean_ctor_get(v_v_684_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v_v_684_);
if (v_isSharedCheck_714_ == 0)
{
v___x_692_ = v_v_684_;
v_isShared_693_ = v_isSharedCheck_714_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_code_690_);
lean_dec(v_v_684_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_714_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; 
v___x_694_ = lean_apply_6(v_f_683_, v_code_690_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, lean_box(0));
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_705_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_705_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v_a_695_);
v___x_700_ = v___x_692_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_704_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_700_);
v___x_702_ = v___x_697_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
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
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_del_object(v___x_692_);
v_a_706_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_694_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_694_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
else
{
lean_object* v___x_715_; 
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec_ref(v_f_683_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v_v_684_);
return v___x_715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg___boxed(lean_object* v_f_716_, lean_object* v_v_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v_f_716_, v_v_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0(uint8_t v_pu_724_, lean_object* v_f_725_, lean_object* v_v_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v_f_725_, v_v_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___boxed(lean_object* v_pu_733_, lean_object* v_f_734_, lean_object* v_v_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
uint8_t v_pu_boxed_741_; lean_object* v_res_742_; 
v_pu_boxed_741_ = lean_unbox(v_pu_733_);
v_res_742_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0(v_pu_boxed_741_, v_f_734_, v_v_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
return v_res_742_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = lean_box(0);
v___x_745_ = lean_unsigned_to_nat(16u);
v___x_746_ = lean_mk_array(v___x_745_, v___x_744_);
return v___x_746_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1);
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v___x_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj(lean_object* v_decl_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_toSignature_756_; lean_object* v_value_757_; uint8_t v_recursive_758_; lean_object* v_inlineAttr_x3f_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_781_; 
v_toSignature_756_ = lean_ctor_get(v_decl_750_, 0);
v_value_757_ = lean_ctor_get(v_decl_750_, 1);
v_recursive_758_ = lean_ctor_get_uint8(v_decl_750_, sizeof(void*)*3);
v_inlineAttr_x3f_759_ = lean_ctor_get(v_decl_750_, 2);
v_isSharedCheck_781_ = !lean_is_exclusive(v_decl_750_);
if (v_isSharedCheck_781_ == 0)
{
v___x_761_ = v_decl_750_;
v_isShared_762_ = v_isSharedCheck_781_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_inlineAttr_x3f_759_);
lean_inc(v_value_757_);
lean_inc(v_toSignature_756_);
lean_dec(v_decl_750_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_781_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___f_763_; lean_object* v___x_764_; 
v___f_763_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0));
lean_inc(v_a_754_);
lean_inc_ref(v_a_753_);
lean_inc(v_a_752_);
lean_inc_ref(v_a_751_);
v___x_764_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v___f_763_, v_value_757_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; uint8_t v___x_766_; lean_object* v___x_768_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref(v___x_764_);
v___x_766_ = 1;
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v_a_765_);
v___x_768_ = v___x_761_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_toSignature_756_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_inlineAttr_x3f_759_);
lean_ctor_set_uint8(v_reuseFailAlloc_772_, sizeof(void*)*3, v_recursive_758_);
v___x_768_ = v_reuseFailAlloc_772_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; 
v___x_769_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2);
v___x_770_ = 0;
v___x_771_ = l_Lean_Compiler_LCNF_Decl_internalize(v___x_766_, v___x_768_, v___x_769_, v___x_770_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
return v___x_771_;
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_del_object(v___x_761_);
lean_dec(v_inlineAttr_x3f_759_);
lean_dec_ref(v_toSignature_756_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
v_a_773_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_764_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_764_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___boxed(lean_object* v_decl_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj(v_decl_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_pushProj(lean_object* v_occurrence_793_){
_start:
{
lean_object* v___x_794_; uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_794_ = ((lean_object*)(l_Lean_Compiler_LCNF_pushProj___closed__1));
v___x_795_ = 2;
v___x_796_ = ((lean_object*)(l_Lean_Compiler_LCNF_pushProj___closed__2));
v___x_797_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_794_, v___x_795_, v___x_796_, v_occurrence_793_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_868_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_));
v___x_869_ = 1;
v___x_870_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_));
v___x_871_ = l_Lean_registerTraceClass(v___x_868_, v___x_869_, v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2____boxed(lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_();
return v_res_873_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PushProj(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_PushProj(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PushProj(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PushProj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_PushProj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_PushProj(builtin);
}
#ifdef __cplusplus
}
#endif
