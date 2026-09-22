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
extern lean_object* l_Lean_instInhabitedFVarIdHashSet;
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_collectUsed(uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
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
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
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
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0(lean_object* v___x_91_, lean_object* v_altsUsed_92_, lean_object* v___x_93_, lean_object* v_fvar_94_, lean_object* v_b_95_, lean_object* v_k_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_array_get_borrowed(v___x_91_, v_altsUsed_92_, v___x_93_);
v___x_103_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v___x_102_, v_fvar_94_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
lean_dec_ref(v_b_95_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v_k_96_);
return v___x_104_;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_mk_empty_array_with_capacity(v___x_105_);
v___x_107_ = lean_array_push(v___x_106_, v_b_95_);
v___x_108_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___x_107_, v_k_96_);
lean_dec_ref(v___x_107_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0___boxed(lean_object* v___x_110_, lean_object* v_altsUsed_111_, lean_object* v___x_112_, lean_object* v_fvar_113_, lean_object* v_b_114_, lean_object* v_k_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0(v___x_110_, v_altsUsed_111_, v___x_112_, v_fvar_113_, v_b_114_, v_k_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v_fvar_113_);
lean_dec(v___x_112_);
lean_dec_ref(v_altsUsed_111_);
lean_dec_ref(v___x_110_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(lean_object* v_altsUsed_122_, lean_object* v_fvar_123_, lean_object* v_b_124_, size_t v_sz_125_, size_t v_i_126_, lean_object* v_bs_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
uint8_t v___x_133_; 
v___x_133_ = lean_usize_dec_lt(v_i_126_, v_sz_125_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
lean_dec_ref(v_b_124_);
lean_dec(v_fvar_123_);
lean_dec_ref(v_altsUsed_122_);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v_bs_127_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v_v_136_; lean_object* v___x_137_; lean_object* v_bs_x27_138_; lean_object* v___x_139_; lean_object* v___f_140_; lean_object* v___x_141_; 
v___x_135_ = l_Lean_instInhabitedFVarIdHashSet;
v_v_136_ = lean_array_uget(v_bs_127_, v_i_126_);
v___x_137_ = lean_unsigned_to_nat(0u);
v_bs_x27_138_ = lean_array_uset(v_bs_127_, v_i_126_, v___x_137_);
v___x_139_ = lean_usize_to_nat(v_i_126_);
lean_inc_ref(v_b_124_);
lean_inc(v_fvar_123_);
lean_inc_ref(v_altsUsed_122_);
v___f_140_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_140_, 0, v___x_135_);
lean_closure_set(v___f_140_, 1, v_altsUsed_122_);
lean_closure_set(v___f_140_, 2, v___x_139_);
lean_closure_set(v___f_140_, 3, v_fvar_123_);
lean_closure_set(v___f_140_, 4, v_b_124_);
v___x_141_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v_v_136_, v___f_140_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; size_t v___x_143_; size_t v___x_144_; lean_object* v___x_145_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_a_142_);
lean_dec_ref_known(v___x_141_, 1);
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_add(v_i_126_, v___x_143_);
v___x_145_ = lean_array_uset(v_bs_x27_138_, v_i_126_, v_a_142_);
v_i_126_ = v___x_144_;
v_bs_127_ = v___x_145_;
goto _start;
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec_ref(v_bs_x27_138_);
lean_dec_ref(v_b_124_);
lean_dec(v_fvar_123_);
lean_dec_ref(v_altsUsed_122_);
v_a_147_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_141_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_141_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___boxed(lean_object* v_altsUsed_155_, lean_object* v_fvar_156_, lean_object* v_b_157_, lean_object* v_sz_158_, lean_object* v_i_159_, lean_object* v_bs_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
size_t v_sz_boxed_166_; size_t v_i_boxed_167_; lean_object* v_res_168_; 
v_sz_boxed_166_ = lean_unbox_usize(v_sz_158_);
lean_dec(v_sz_158_);
v_i_boxed_167_ = lean_unbox_usize(v_i_159_);
lean_dec(v_i_159_);
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_155_, v_fvar_156_, v_b_157_, v_sz_boxed_166_, v_i_boxed_167_, v_bs_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(lean_object* v_fvar_169_, lean_object* v_b_170_, size_t v_sz_171_, size_t v_i_172_, lean_object* v_bs_173_){
_start:
{
uint8_t v___x_174_; 
v___x_174_ = lean_usize_dec_lt(v_i_172_, v_sz_171_);
if (v___x_174_ == 0)
{
lean_dec_ref(v_b_170_);
return v_bs_173_;
}
else
{
lean_object* v_v_175_; lean_object* v___x_176_; lean_object* v_bs_x27_177_; lean_object* v___y_179_; uint8_t v___x_184_; 
v_v_175_ = lean_array_uget(v_bs_173_, v_i_172_);
v___x_176_ = lean_unsigned_to_nat(0u);
v_bs_x27_177_ = lean_array_uset(v_bs_173_, v_i_172_, v___x_176_);
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_v_175_, v_fvar_169_);
if (v___x_184_ == 0)
{
v___y_179_ = v_v_175_;
goto v___jp_178_;
}
else
{
uint8_t v___x_185_; lean_object* v___x_186_; 
v___x_185_ = 1;
lean_inc_ref(v_b_170_);
v___x_186_ = l_Lean_Compiler_LCNF_CodeDecl_collectUsed(v___x_185_, v_b_170_, v_v_175_);
v___y_179_ = v___x_186_;
goto v___jp_178_;
}
v___jp_178_:
{
size_t v___x_180_; size_t v___x_181_; lean_object* v___x_182_; 
v___x_180_ = ((size_t)1ULL);
v___x_181_ = lean_usize_add(v_i_172_, v___x_180_);
v___x_182_ = lean_array_uset(v_bs_x27_177_, v_i_172_, v___y_179_);
v_i_172_ = v___x_181_;
v_bs_173_ = v___x_182_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3___boxed(lean_object* v_fvar_187_, lean_object* v_b_188_, lean_object* v_sz_189_, lean_object* v_i_190_, lean_object* v_bs_191_){
_start:
{
size_t v_sz_boxed_192_; size_t v_i_boxed_193_; lean_object* v_res_194_; 
v_sz_boxed_192_ = lean_unbox_usize(v_sz_189_);
lean_dec(v_sz_189_);
v_i_boxed_193_ = lean_unbox_usize(v_i_190_);
lean_dec(v_i_190_);
v_res_194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(v_fvar_187_, v_b_188_, v_sz_boxed_192_, v_i_boxed_193_, v_bs_191_);
lean_dec(v_fvar_187_);
return v_res_194_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0(void){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(lean_object* v_decls_196_, lean_object* v_alts_197_, lean_object* v_altsUsed_198_, lean_object* v_ctx_199_, lean_object* v_ctxUsed_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_206_ = lean_array_get_size(v_decls_196_);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_nat_dec_eq(v___x_206_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v_b_212_; lean_object* v_bs_213_; 
v___x_209_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0);
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_sub(v___x_206_, v___x_210_);
v_b_212_ = lean_array_get(v___x_209_, v_decls_196_, v___x_211_);
lean_dec(v___x_211_);
v_bs_213_ = lean_array_pop(v_decls_196_);
if (lean_obj_tag(v_b_212_) == 0)
{
lean_object* v_decl_220_; lean_object* v_fvarId_221_; lean_object* v_value_222_; uint8_t v___x_223_; lean_object* v_fvar_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; 
v_decl_220_ = lean_ctor_get(v_b_212_, 0);
v_fvarId_221_ = lean_ctor_get(v_decl_220_, 0);
v_value_222_ = lean_ctor_get(v_decl_220_, 3);
v___x_223_ = 1;
switch(lean_obj_tag(v_value_222_))
{
case 7:
{
lean_inc(v_fvarId_221_);
v_fvar_225_ = v_fvarId_221_;
v___y_226_ = v_a_201_;
v___y_227_ = v_a_202_;
v___y_228_ = v_a_203_;
v___y_229_ = v_a_204_;
goto v___jp_224_;
}
case 6:
{
lean_inc(v_fvarId_221_);
v_fvar_225_ = v_fvarId_221_;
v___y_226_ = v_a_201_;
v___y_227_ = v_a_202_;
v___y_228_ = v_a_203_;
v___y_229_ = v_a_204_;
goto v___jp_224_;
}
case 8:
{
lean_inc(v_fvarId_221_);
v_fvar_225_ = v_fvarId_221_;
v___y_226_ = v_a_201_;
v___y_227_ = v_a_202_;
v___y_228_ = v_a_203_;
v___y_229_ = v_a_204_;
goto v___jp_224_;
}
default: 
{
lean_dec_ref(v_ctxUsed_200_);
lean_dec_ref(v_altsUsed_198_);
goto v___jp_214_;
}
}
v___jp_224_:
{
uint8_t v___x_230_; 
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_ctxUsed_200_, v_fvar_225_);
if (v___x_230_ == 0)
{
size_t v_sz_231_; size_t v___x_232_; lean_object* v___x_233_; 
v_sz_231_ = lean_array_size(v_alts_197_);
v___x_232_ = ((size_t)0ULL);
lean_inc_ref(v_b_212_);
lean_inc(v_fvar_225_);
lean_inc_ref(v_altsUsed_198_);
v___x_233_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_198_, v_fvar_225_, v_b_212_, v_sz_231_, v___x_232_, v_alts_197_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; size_t v_sz_235_; lean_object* v___x_236_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v___x_233_, 1);
v_sz_235_ = lean_array_size(v_altsUsed_198_);
v___x_236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(v_fvar_225_, v_b_212_, v_sz_235_, v___x_232_, v_altsUsed_198_);
lean_dec(v_fvar_225_);
v_decls_196_ = v_bs_213_;
v_alts_197_ = v_a_234_;
v_altsUsed_198_ = v___x_236_;
v_a_201_ = v___y_226_;
v_a_202_ = v___y_227_;
v_a_203_ = v___y_228_;
v_a_204_ = v___y_229_;
goto _start;
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec(v_fvar_225_);
lean_dec_ref_known(v_b_212_, 1);
lean_dec_ref(v_bs_213_);
lean_dec_ref(v_ctxUsed_200_);
lean_dec_ref(v_ctx_199_);
lean_dec_ref(v_altsUsed_198_);
v_a_238_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_233_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_233_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v_fvar_225_);
lean_inc_ref(v_b_212_);
v___x_246_ = lean_array_push(v_ctx_199_, v_b_212_);
v___x_247_ = l_Lean_Compiler_LCNF_CodeDecl_collectUsed(v___x_223_, v_b_212_, v_ctxUsed_200_);
v_decls_196_ = v_bs_213_;
v_ctx_199_ = v___x_246_;
v_ctxUsed_200_ = v___x_247_;
v_a_201_ = v___y_226_;
v_a_202_ = v___y_227_;
v_a_203_ = v___y_228_;
v_a_204_ = v___y_229_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_ctxUsed_200_);
lean_dec_ref(v_altsUsed_198_);
goto v___jp_214_;
}
v___jp_214_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_215_ = lean_array_push(v_bs_213_, v_b_212_);
v___x_216_ = l_Array_reverse___redArg(v_ctx_199_);
v___x_217_ = l_Array_append___redArg(v___x_215_, v___x_216_);
lean_dec_ref(v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v_alts_197_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec_ref(v_ctxUsed_200_);
lean_dec_ref(v_altsUsed_198_);
lean_dec_ref(v_decls_196_);
v___x_249_ = l_Array_reverse___redArg(v_ctx_199_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v_alts_197_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___boxed(lean_object* v_decls_252_, lean_object* v_alts_253_, lean_object* v_altsUsed_254_, lean_object* v_ctx_255_, lean_object* v_ctxUsed_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(v_decls_252_, v_alts_253_, v_altsUsed_254_, v_ctx_255_, v_ctxUsed_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
return v_res_262_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0(lean_object* v_00_u03b2_263_, lean_object* v_m_264_, lean_object* v_a_265_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_m_264_, v_a_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___boxed(lean_object* v_00_u03b2_267_, lean_object* v_m_268_, lean_object* v_a_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0(v_00_u03b2_267_, v_m_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec_ref(v_m_268_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2(lean_object* v_altsUsed_272_, lean_object* v_fvar_273_, lean_object* v_b_274_, lean_object* v_as_275_, size_t v_sz_276_, size_t v_i_277_, lean_object* v_bs_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_272_, v_fvar_273_, v_b_274_, v_sz_276_, v_i_277_, v_bs_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___boxed(lean_object* v_altsUsed_285_, lean_object* v_fvar_286_, lean_object* v_b_287_, lean_object* v_as_288_, lean_object* v_sz_289_, lean_object* v_i_290_, lean_object* v_bs_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
size_t v_sz_boxed_297_; size_t v_i_boxed_298_; lean_object* v_res_299_; 
v_sz_boxed_297_ = lean_unbox_usize(v_sz_289_);
lean_dec(v_sz_289_);
v_i_boxed_298_ = lean_unbox_usize(v_i_290_);
lean_dec(v_i_290_);
v_res_299_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2(v_altsUsed_285_, v_fvar_286_, v_b_287_, v_as_288_, v_sz_boxed_297_, v_i_boxed_298_, v_bs_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec_ref(v_as_288_);
return v_res_299_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0(lean_object* v_00_u03b2_300_, lean_object* v_a_301_, lean_object* v_x_302_){
_start:
{
uint8_t v___x_303_; 
v___x_303_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_301_, v_x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_304_, lean_object* v_a_305_, lean_object* v_x_306_){
_start:
{
uint8_t v_res_307_; lean_object* v_r_308_; 
v_res_307_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0(v_00_u03b2_304_, v_a_305_, v_x_306_);
lean_dec(v_x_306_);
lean_dec(v_a_305_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(size_t v_sz_309_, size_t v_i_310_, lean_object* v_bs_311_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = lean_usize_dec_lt(v_i_310_, v_sz_309_);
if (v___x_312_ == 0)
{
return v_bs_311_;
}
else
{
lean_object* v___x_313_; lean_object* v_v_314_; lean_object* v___x_315_; lean_object* v_bs_x27_316_; uint8_t v___x_317_; lean_object* v___y_319_; 
v___x_313_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v_v_314_ = lean_array_uget(v_bs_311_, v_i_310_);
v___x_315_ = lean_unsigned_to_nat(0u);
v_bs_x27_316_ = lean_array_uset(v_bs_311_, v_i_310_, v___x_315_);
v___x_317_ = 1;
switch(lean_obj_tag(v_v_314_))
{
case 0:
{
lean_object* v_code_325_; 
v_code_325_ = lean_ctor_get(v_v_314_, 2);
lean_inc_ref(v_code_325_);
lean_dec_ref_known(v_v_314_, 3);
v___y_319_ = v_code_325_;
goto v___jp_318_;
}
case 1:
{
lean_object* v_code_326_; 
v_code_326_ = lean_ctor_get(v_v_314_, 1);
lean_inc_ref(v_code_326_);
lean_dec_ref_known(v_v_314_, 2);
v___y_319_ = v_code_326_;
goto v___jp_318_;
}
default: 
{
lean_object* v_code_327_; 
v_code_327_ = lean_ctor_get(v_v_314_, 0);
lean_inc_ref(v_code_327_);
lean_dec_ref_known(v_v_314_, 1);
v___y_319_ = v_code_327_;
goto v___jp_318_;
}
}
v___jp_318_:
{
lean_object* v___x_320_; size_t v___x_321_; size_t v___x_322_; lean_object* v___x_323_; 
v___x_320_ = l_Lean_Compiler_LCNF_Code_collectUsed(v___x_317_, v___y_319_, v___x_313_);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_add(v_i_310_, v___x_321_);
v___x_323_ = lean_array_uset(v_bs_x27_316_, v_i_310_, v___x_320_);
v_i_310_ = v___x_322_;
v_bs_311_ = v___x_323_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1___boxed(lean_object* v_sz_328_, lean_object* v_i_329_, lean_object* v_bs_330_){
_start:
{
size_t v_sz_boxed_331_; size_t v_i_boxed_332_; lean_object* v_res_333_; 
v_sz_boxed_331_ = lean_unbox_usize(v_sz_328_);
lean_dec(v_sz_328_);
v_i_boxed_332_ = lean_unbox_usize(v_i_329_);
lean_dec(v_i_329_);
v_res_333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(v_sz_boxed_331_, v_i_boxed_332_, v_bs_330_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
return v_x_334_;
}
else
{
lean_object* v_key_336_; lean_object* v_value_337_; lean_object* v_tail_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_361_; 
v_key_336_ = lean_ctor_get(v_x_335_, 0);
v_value_337_ = lean_ctor_get(v_x_335_, 1);
v_tail_338_ = lean_ctor_get(v_x_335_, 2);
v_isSharedCheck_361_ = !lean_is_exclusive(v_x_335_);
if (v_isSharedCheck_361_ == 0)
{
v___x_340_ = v_x_335_;
v_isShared_341_ = v_isSharedCheck_361_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_tail_338_);
lean_inc(v_value_337_);
lean_inc(v_key_336_);
lean_dec(v_x_335_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_361_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; uint64_t v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; uint64_t v_fold_346_; uint64_t v___x_347_; uint64_t v___x_348_; uint64_t v___x_349_; size_t v___x_350_; size_t v___x_351_; size_t v___x_352_; size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_342_ = lean_array_get_size(v_x_334_);
v___x_343_ = l_Lean_instHashableFVarId_hash(v_key_336_);
v___x_344_ = 32ULL;
v___x_345_ = lean_uint64_shift_right(v___x_343_, v___x_344_);
v_fold_346_ = lean_uint64_xor(v___x_343_, v___x_345_);
v___x_347_ = 16ULL;
v___x_348_ = lean_uint64_shift_right(v_fold_346_, v___x_347_);
v___x_349_ = lean_uint64_xor(v_fold_346_, v___x_348_);
v___x_350_ = lean_uint64_to_usize(v___x_349_);
v___x_351_ = lean_usize_of_nat(v___x_342_);
v___x_352_ = ((size_t)1ULL);
v___x_353_ = lean_usize_sub(v___x_351_, v___x_352_);
v___x_354_ = lean_usize_land(v___x_350_, v___x_353_);
v___x_355_ = lean_array_uget_borrowed(v_x_334_, v___x_354_);
lean_inc(v___x_355_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 2, v___x_355_);
v___x_357_ = v___x_340_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_key_336_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_value_337_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v___x_355_);
v___x_357_ = v_reuseFailAlloc_360_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; 
v___x_358_ = lean_array_uset(v_x_334_, v___x_354_, v___x_357_);
v_x_334_ = v___x_358_;
v_x_335_ = v_tail_338_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4___redArg(lean_object* v_i_362_, lean_object* v_source_363_, lean_object* v_target_364_){
_start:
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_array_get_size(v_source_363_);
v___x_366_ = lean_nat_dec_lt(v_i_362_, v___x_365_);
if (v___x_366_ == 0)
{
lean_dec_ref(v_source_363_);
lean_dec(v_i_362_);
return v_target_364_;
}
else
{
lean_object* v_es_367_; lean_object* v___x_368_; lean_object* v_source_369_; lean_object* v_target_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_es_367_ = lean_array_fget(v_source_363_, v_i_362_);
v___x_368_ = lean_box(0);
v_source_369_ = lean_array_fset(v_source_363_, v_i_362_, v___x_368_);
v_target_370_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6___redArg(v_target_364_, v_es_367_);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_add(v_i_362_, v___x_371_);
lean_dec(v_i_362_);
v_i_362_ = v___x_372_;
v_source_363_ = v_source_369_;
v_target_364_ = v_target_370_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3___redArg(lean_object* v_data_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v_nbuckets_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_375_ = lean_array_get_size(v_data_374_);
v___x_376_ = lean_unsigned_to_nat(2u);
v_nbuckets_377_ = lean_nat_mul(v___x_375_, v___x_376_);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_box(0);
v___x_380_ = lean_mk_array(v_nbuckets_377_, v___x_379_);
v___x_381_ = lean_array_propagate_mark(v_data_374_, v___x_380_);
v___x_382_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4___redArg(v___x_378_, v_data_374_, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___redArg(lean_object* v_m_383_, lean_object* v_a_384_, lean_object* v_b_385_){
_start:
{
lean_object* v_size_386_; lean_object* v_buckets_387_; lean_object* v___x_388_; uint64_t v___x_389_; uint64_t v___x_390_; uint64_t v___x_391_; uint64_t v_fold_392_; uint64_t v___x_393_; uint64_t v___x_394_; uint64_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; size_t v___x_400_; lean_object* v_bkt_401_; uint8_t v___x_402_; 
v_size_386_ = lean_ctor_get(v_m_383_, 0);
v_buckets_387_ = lean_ctor_get(v_m_383_, 1);
v___x_388_ = lean_array_get_size(v_buckets_387_);
v___x_389_ = l_Lean_instHashableFVarId_hash(v_a_384_);
v___x_390_ = 32ULL;
v___x_391_ = lean_uint64_shift_right(v___x_389_, v___x_390_);
v_fold_392_ = lean_uint64_xor(v___x_389_, v___x_391_);
v___x_393_ = 16ULL;
v___x_394_ = lean_uint64_shift_right(v_fold_392_, v___x_393_);
v___x_395_ = lean_uint64_xor(v_fold_392_, v___x_394_);
v___x_396_ = lean_uint64_to_usize(v___x_395_);
v___x_397_ = lean_usize_of_nat(v___x_388_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_sub(v___x_397_, v___x_398_);
v___x_400_ = lean_usize_land(v___x_396_, v___x_399_);
v_bkt_401_ = lean_array_uget_borrowed(v_buckets_387_, v___x_400_);
v___x_402_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_384_, v_bkt_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_423_; 
lean_inc_ref(v_buckets_387_);
lean_inc(v_size_386_);
v_isSharedCheck_423_ = !lean_is_exclusive(v_m_383_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; lean_object* v_unused_425_; 
v_unused_424_ = lean_ctor_get(v_m_383_, 1);
lean_dec(v_unused_424_);
v_unused_425_ = lean_ctor_get(v_m_383_, 0);
lean_dec(v_unused_425_);
v___x_404_ = v_m_383_;
v_isShared_405_ = v_isSharedCheck_423_;
goto v_resetjp_403_;
}
else
{
lean_dec(v_m_383_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_423_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v_size_x27_407_; lean_object* v___x_408_; lean_object* v_buckets_x27_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_406_ = lean_unsigned_to_nat(1u);
v_size_x27_407_ = lean_nat_add(v_size_386_, v___x_406_);
lean_dec(v_size_386_);
lean_inc(v_bkt_401_);
v___x_408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_408_, 0, v_a_384_);
lean_ctor_set(v___x_408_, 1, v_b_385_);
lean_ctor_set(v___x_408_, 2, v_bkt_401_);
v_buckets_x27_409_ = lean_array_uset(v_buckets_387_, v___x_400_, v___x_408_);
v___x_410_ = lean_unsigned_to_nat(4u);
v___x_411_ = lean_nat_mul(v_size_x27_407_, v___x_410_);
v___x_412_ = lean_unsigned_to_nat(3u);
v___x_413_ = lean_nat_div(v___x_411_, v___x_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_array_get_size(v_buckets_x27_409_);
v___x_415_ = lean_nat_dec_le(v___x_413_, v___x_414_);
lean_dec(v___x_413_);
if (v___x_415_ == 0)
{
lean_object* v_val_416_; lean_object* v___x_418_; 
v_val_416_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3___redArg(v_buckets_x27_409_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v_val_416_);
lean_ctor_set(v___x_404_, 0, v_size_x27_407_);
v___x_418_ = v___x_404_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_size_x27_407_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_val_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
else
{
lean_object* v___x_421_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v_buckets_x27_409_);
lean_ctor_set(v___x_404_, 0, v_size_x27_407_);
v___x_421_ = v___x_404_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_size_x27_407_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_buckets_x27_409_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
else
{
lean_dec(v_b_385_);
lean_dec(v_a_384_);
return v_m_383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed(lean_object* v_code_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(v_code_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(lean_object* v_i_435_, lean_object* v_as_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_array_get_size(v_as_436_);
v___x_443_ = lean_nat_dec_lt(v_i_435_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
lean_dec(v_i_435_);
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v_as_436_);
return v___x_444_;
}
else
{
lean_object* v_a_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_a_445_ = lean_array_fget_borrowed(v_as_436_, v_i_435_);
v___x_446_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed), 6, 0);
lean_inc(v_a_445_);
v___x_447_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v_a_445_, v___x_446_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; size_t v___x_449_; size_t v___x_450_; uint8_t v___x_451_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = lean_ptr_addr(v_a_445_);
v___x_450_ = lean_ptr_addr(v_a_448_);
v___x_451_ = lean_usize_dec_eq(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_unsigned_to_nat(1u);
v___x_453_ = lean_nat_add(v_i_435_, v___x_452_);
v___x_454_ = lean_array_fset(v_as_436_, v_i_435_, v_a_448_);
lean_dec(v_i_435_);
v_i_435_ = v___x_453_;
v_as_436_ = v___x_454_;
goto _start;
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v_a_448_);
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_nat_add(v_i_435_, v___x_456_);
lean_dec(v_i_435_);
v_i_435_ = v___x_457_;
goto _start;
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec_ref(v_as_436_);
lean_dec(v_i_435_);
v_a_459_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_447_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_447_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(lean_object* v_c_467_, lean_object* v_decls_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_typeName_474_; lean_object* v_resultType_475_; lean_object* v_discr_476_; lean_object* v_alts_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_523_; 
v_typeName_474_ = lean_ctor_get(v_c_467_, 0);
v_resultType_475_ = lean_ctor_get(v_c_467_, 1);
v_discr_476_ = lean_ctor_get(v_c_467_, 2);
v_alts_477_ = lean_ctor_get(v_c_467_, 3);
v_isSharedCheck_523_ = !lean_is_exclusive(v_c_467_);
if (v_isSharedCheck_523_ == 0)
{
v___x_479_ = v_c_467_;
v_isShared_480_ = v_isSharedCheck_523_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_alts_477_);
lean_inc(v_discr_476_);
lean_inc(v_resultType_475_);
lean_inc(v_typeName_474_);
lean_dec(v_c_467_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_523_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; size_t v_sz_482_; size_t v___x_483_; lean_object* v_altsUsed_484_; lean_object* v___x_485_; lean_object* v_ctxUsed_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_481_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v_sz_482_ = lean_array_size(v_alts_477_);
v___x_483_ = ((size_t)0ULL);
lean_inc_ref(v_alts_477_);
v_altsUsed_484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(v_sz_482_, v___x_483_, v_alts_477_);
v___x_485_ = lean_box(0);
lean_inc(v_discr_476_);
v_ctxUsed_486_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___redArg(v___x_481_, v_discr_476_, v___x_485_);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0));
v___x_489_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(v_decls_468_, v_alts_477_, v_altsUsed_484_, v___x_488_, v_ctxUsed_486_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v_fst_491_; lean_object* v_snd_492_; lean_object* v___x_493_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v_fst_491_ = lean_ctor_get(v_a_490_, 0);
lean_inc(v_fst_491_);
v_snd_492_ = lean_ctor_get(v_a_490_, 1);
lean_inc(v_snd_492_);
lean_dec(v_a_490_);
v___x_493_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(v___x_487_, v_snd_492_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_506_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_506_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_506_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_506_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 3, v_a_494_);
v___x_499_ = v___x_479_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_typeName_474_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_resultType_475_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_discr_476_);
lean_ctor_set(v_reuseFailAlloc_505_, 3, v_a_494_);
v___x_499_ = v_reuseFailAlloc_505_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_500_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
v___x_501_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_fst_491_, v___x_500_);
lean_dec(v_fst_491_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_501_);
v___x_503_ = v___x_496_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec(v_fst_491_);
lean_del_object(v___x_479_);
lean_dec(v_discr_476_);
lean_dec_ref(v_resultType_475_);
lean_dec(v_typeName_474_);
v_a_507_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_493_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_493_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_del_object(v___x_479_);
lean_dec(v_discr_476_);
lean_dec_ref(v_resultType_475_);
lean_dec(v_typeName_474_);
v_a_515_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_489_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_489_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(lean_object* v_c_524_, lean_object* v_decls_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
switch(lean_obj_tag(v_c_524_))
{
case 0:
{
lean_object* v_decl_531_; lean_object* v_k_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_decl_531_ = lean_ctor_get(v_c_524_, 0);
lean_inc_ref(v_decl_531_);
v_k_532_ = lean_ctor_get(v_c_524_, 1);
lean_inc_ref(v_k_532_);
lean_dec_ref_known(v_c_524_, 2);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v_decl_531_);
v___x_534_ = lean_array_push(v_decls_525_, v___x_533_);
v_c_524_ = v_k_532_;
v_decls_525_ = v___x_534_;
goto _start;
}
case 2:
{
lean_object* v_decl_536_; lean_object* v_k_537_; lean_object* v_params_538_; lean_object* v_type_539_; lean_object* v_value_540_; uint8_t v___x_541_; lean_object* v___x_542_; 
v_decl_536_ = lean_ctor_get(v_c_524_, 0);
lean_inc_ref(v_decl_536_);
v_k_537_ = lean_ctor_get(v_c_524_, 1);
lean_inc_ref(v_k_537_);
lean_dec_ref_known(v_c_524_, 2);
v_params_538_ = lean_ctor_get(v_decl_536_, 2);
lean_inc_ref(v_params_538_);
v_type_539_ = lean_ctor_get(v_decl_536_, 3);
lean_inc_ref(v_type_539_);
v_value_540_ = lean_ctor_get(v_decl_536_, 4);
v___x_541_ = 1;
lean_inc_ref(v_value_540_);
v___x_542_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(v_value_540_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_562_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_562_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_562_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_562_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; 
v___x_547_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_541_, v_decl_536_, v_type_539_, v_params_538_, v_a_543_, v_a_527_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_550_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_547_, 1);
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 2);
lean_ctor_set(v___x_545_, 0, v_a_548_);
v___x_550_ = v___x_545_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_548_);
v___x_550_ = v_reuseFailAlloc_553_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; 
v___x_551_ = lean_array_push(v_decls_525_, v___x_550_);
v_c_524_ = v_k_537_;
v_decls_525_ = v___x_551_;
goto _start;
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_del_object(v___x_545_);
lean_dec_ref(v_k_537_);
lean_dec_ref(v_decls_525_);
v_a_554_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_547_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_547_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_539_);
lean_dec_ref(v_params_538_);
lean_dec_ref(v_k_537_);
lean_dec_ref(v_decl_536_);
lean_dec_ref(v_decls_525_);
return v___x_542_;
}
}
case 4:
{
lean_object* v_cases_563_; lean_object* v___x_564_; 
v_cases_563_ = lean_ctor_get(v_c_524_, 0);
lean_inc_ref(v_cases_563_);
lean_dec_ref_known(v_c_524_, 1);
v___x_564_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(v_cases_563_, v_decls_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
return v___x_564_;
}
case 7:
{
lean_object* v_fvarId_565_; lean_object* v_i_566_; lean_object* v_y_567_; lean_object* v_k_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_fvarId_565_ = lean_ctor_get(v_c_524_, 0);
lean_inc(v_fvarId_565_);
v_i_566_ = lean_ctor_get(v_c_524_, 1);
lean_inc(v_i_566_);
v_y_567_ = lean_ctor_get(v_c_524_, 2);
lean_inc(v_y_567_);
v_k_568_ = lean_ctor_get(v_c_524_, 3);
lean_inc_ref(v_k_568_);
lean_dec_ref_known(v_c_524_, 4);
v___x_569_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_569_, 0, v_fvarId_565_);
lean_ctor_set(v___x_569_, 1, v_i_566_);
lean_ctor_set(v___x_569_, 2, v_y_567_);
v___x_570_ = lean_array_push(v_decls_525_, v___x_569_);
v_c_524_ = v_k_568_;
v_decls_525_ = v___x_570_;
goto _start;
}
case 8:
{
lean_object* v_fvarId_572_; lean_object* v_i_573_; lean_object* v_y_574_; lean_object* v_k_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_fvarId_572_ = lean_ctor_get(v_c_524_, 0);
lean_inc(v_fvarId_572_);
v_i_573_ = lean_ctor_get(v_c_524_, 1);
lean_inc(v_i_573_);
v_y_574_ = lean_ctor_get(v_c_524_, 2);
lean_inc(v_y_574_);
v_k_575_ = lean_ctor_get(v_c_524_, 3);
lean_inc_ref(v_k_575_);
lean_dec_ref_known(v_c_524_, 4);
v___x_576_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_576_, 0, v_fvarId_572_);
lean_ctor_set(v___x_576_, 1, v_i_573_);
lean_ctor_set(v___x_576_, 2, v_y_574_);
v___x_577_ = lean_array_push(v_decls_525_, v___x_576_);
v_c_524_ = v_k_575_;
v_decls_525_ = v___x_577_;
goto _start;
}
case 9:
{
lean_object* v_fvarId_579_; lean_object* v_i_580_; lean_object* v_offset_581_; lean_object* v_y_582_; lean_object* v_ty_583_; lean_object* v_k_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_fvarId_579_ = lean_ctor_get(v_c_524_, 0);
lean_inc(v_fvarId_579_);
v_i_580_ = lean_ctor_get(v_c_524_, 1);
lean_inc(v_i_580_);
v_offset_581_ = lean_ctor_get(v_c_524_, 2);
lean_inc(v_offset_581_);
v_y_582_ = lean_ctor_get(v_c_524_, 3);
lean_inc(v_y_582_);
v_ty_583_ = lean_ctor_get(v_c_524_, 4);
lean_inc_ref(v_ty_583_);
v_k_584_ = lean_ctor_get(v_c_524_, 5);
lean_inc_ref(v_k_584_);
lean_dec_ref_known(v_c_524_, 6);
v___x_585_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v___x_585_, 0, v_fvarId_579_);
lean_ctor_set(v___x_585_, 1, v_i_580_);
lean_ctor_set(v___x_585_, 2, v_offset_581_);
lean_ctor_set(v___x_585_, 3, v_y_582_);
lean_ctor_set(v___x_585_, 4, v_ty_583_);
v___x_586_ = lean_array_push(v_decls_525_, v___x_585_);
v_c_524_ = v_k_584_;
v_decls_525_ = v___x_586_;
goto _start;
}
case 10:
{
lean_object* v_fvarId_588_; lean_object* v_cidx_589_; lean_object* v_k_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_fvarId_588_ = lean_ctor_get(v_c_524_, 0);
lean_inc(v_fvarId_588_);
v_cidx_589_ = lean_ctor_get(v_c_524_, 1);
lean_inc(v_cidx_589_);
v_k_590_ = lean_ctor_get(v_c_524_, 2);
lean_inc_ref(v_k_590_);
lean_dec_ref_known(v_c_524_, 3);
v___x_591_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_591_, 0, v_fvarId_588_);
lean_ctor_set(v___x_591_, 1, v_cidx_589_);
v___x_592_ = lean_array_push(v_decls_525_, v___x_591_);
v_c_524_ = v_k_590_;
v_decls_525_ = v___x_592_;
goto _start;
}
case 11:
{
lean_object* v_fvarId_594_; lean_object* v_n_595_; uint8_t v_check_596_; uint8_t v_persistent_597_; lean_object* v_k_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v_fvarId_594_ = lean_ctor_get(v_c_524_, 0);
lean_inc(v_fvarId_594_);
v_n_595_ = lean_ctor_get(v_c_524_, 1);
lean_inc(v_n_595_);
v_check_596_ = lean_ctor_get_uint8(v_c_524_, sizeof(void*)*3);
v_persistent_597_ = lean_ctor_get_uint8(v_c_524_, sizeof(void*)*3 + 1);
v_k_598_ = lean_ctor_get(v_c_524_, 2);
lean_inc_ref(v_k_598_);
lean_dec_ref_known(v_c_524_, 3);
v___x_599_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v___x_599_, 0, v_fvarId_594_);
lean_ctor_set(v___x_599_, 1, v_n_595_);
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*2, v_check_596_);
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*2 + 1, v_persistent_597_);
v___x_600_ = lean_array_push(v_decls_525_, v___x_599_);
v_c_524_ = v_k_598_;
v_decls_525_ = v___x_600_;
goto _start;
}
case 12:
{
lean_object* v_fvarId_602_; lean_object* v_n_603_; uint8_t v_check_604_; uint8_t v_persistent_605_; lean_object* v_objs_x3f_606_; lean_object* v_k_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_fvarId_602_ = lean_ctor_get(v_c_524_, 0);
lean_inc(v_fvarId_602_);
v_n_603_ = lean_ctor_get(v_c_524_, 1);
lean_inc(v_n_603_);
v_check_604_ = lean_ctor_get_uint8(v_c_524_, sizeof(void*)*4);
v_persistent_605_ = lean_ctor_get_uint8(v_c_524_, sizeof(void*)*4 + 1);
v_objs_x3f_606_ = lean_ctor_get(v_c_524_, 2);
lean_inc(v_objs_x3f_606_);
v_k_607_ = lean_ctor_get(v_c_524_, 3);
lean_inc_ref(v_k_607_);
lean_dec_ref_known(v_c_524_, 4);
v___x_608_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v___x_608_, 0, v_fvarId_602_);
lean_ctor_set(v___x_608_, 1, v_n_603_);
lean_ctor_set(v___x_608_, 2, v_objs_x3f_606_);
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*3, v_check_604_);
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*3 + 1, v_persistent_605_);
v___x_609_ = lean_array_push(v_decls_525_, v___x_608_);
v_c_524_ = v_k_607_;
v_decls_525_ = v___x_609_;
goto _start;
}
case 13:
{
lean_object* v_fvarId_611_; lean_object* v_k_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_fvarId_611_ = lean_ctor_get(v_c_524_, 0);
lean_inc(v_fvarId_611_);
v_k_612_ = lean_ctor_get(v_c_524_, 1);
lean_inc_ref(v_k_612_);
lean_dec_ref_known(v_c_524_, 2);
v___x_613_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_613_, 0, v_fvarId_611_);
v___x_614_ = lean_array_push(v_decls_525_, v___x_613_);
v_c_524_ = v_k_612_;
v_decls_525_ = v___x_614_;
goto _start;
}
default: 
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_decls_525_, v_c_524_);
lean_dec_ref(v_decls_525_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(lean_object* v_code_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0));
v___x_625_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(v_code_618_, v___x_624_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___boxed(lean_object* v_i_626_, lean_object* v_as_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(v_i_626_, v_as_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___boxed(lean_object* v_c_634_, lean_object* v_decls_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(v_c_634_, v_decls_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go___boxed(lean_object* v_c_642_, lean_object* v_decls_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(v_c_642_, v_decls_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2(lean_object* v_00_u03b2_650_, lean_object* v_m_651_, lean_object* v_a_652_, lean_object* v_b_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___redArg(v_m_651_, v_a_652_, v_b_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3(lean_object* v_00_u03b2_655_, lean_object* v_data_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3___redArg(v_data_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_658_, lean_object* v_i_659_, lean_object* v_source_660_, lean_object* v_target_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4___redArg(v_i_659_, v_source_660_, v_target_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_663_, lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6___redArg(v_x_664_, v_x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(lean_object* v_f_667_, lean_object* v_v_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
if (lean_obj_tag(v_v_668_) == 0)
{
lean_object* v_code_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_698_; 
v_code_674_ = lean_ctor_get(v_v_668_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v_v_668_);
if (v_isSharedCheck_698_ == 0)
{
v___x_676_ = v_v_668_;
v_isShared_677_ = v_isSharedCheck_698_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_code_674_);
lean_dec(v_v_668_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_698_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; 
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
lean_inc(v___y_670_);
lean_inc_ref(v___y_669_);
v___x_678_ = lean_apply_6(v_f_667_, v_code_674_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, lean_box(0));
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_689_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_689_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v_a_679_);
v___x_684_ = v___x_676_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_688_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_686_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_684_);
v___x_686_ = v___x_681_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_del_object(v___x_676_);
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
else
{
lean_object* v___x_699_; 
lean_dec_ref(v_f_667_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v_v_668_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg___boxed(lean_object* v_f_700_, lean_object* v_v_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v_f_700_, v_v_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0(uint8_t v_pu_708_, lean_object* v_f_709_, lean_object* v_v_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v_f_709_, v_v_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___boxed(lean_object* v_pu_717_, lean_object* v_f_718_, lean_object* v_v_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
uint8_t v_pu_boxed_725_; lean_object* v_res_726_; 
v_pu_boxed_725_ = lean_unbox(v_pu_717_);
v_res_726_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0(v_pu_boxed_725_, v_f_718_, v_v_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v_res_726_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_728_ = lean_box(0);
v___x_729_ = lean_unsigned_to_nat(16u);
v___x_730_ = lean_mk_array(v___x_729_, v___x_728_);
return v___x_730_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1);
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj(lean_object* v_decl_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_toSignature_740_; lean_object* v_value_741_; uint8_t v_recursive_742_; lean_object* v_inlineAttr_x3f_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_765_; 
v_toSignature_740_ = lean_ctor_get(v_decl_734_, 0);
v_value_741_ = lean_ctor_get(v_decl_734_, 1);
v_recursive_742_ = lean_ctor_get_uint8(v_decl_734_, sizeof(void*)*3);
v_inlineAttr_x3f_743_ = lean_ctor_get(v_decl_734_, 2);
v_isSharedCheck_765_ = !lean_is_exclusive(v_decl_734_);
if (v_isSharedCheck_765_ == 0)
{
v___x_745_ = v_decl_734_;
v_isShared_746_ = v_isSharedCheck_765_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_inlineAttr_x3f_743_);
lean_inc(v_value_741_);
lean_inc(v_toSignature_740_);
lean_dec(v_decl_734_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_765_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___f_747_; uint8_t v___x_748_; lean_object* v___x_749_; 
v___f_747_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0));
v___x_748_ = 1;
v___x_749_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v___f_747_, v_value_741_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_749_, 1);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v_a_750_);
v___x_752_ = v___x_745_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_toSignature_740_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_a_750_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_inlineAttr_x3f_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_756_, sizeof(void*)*3, v_recursive_742_);
v___x_752_ = v_reuseFailAlloc_756_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; uint8_t v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2);
v___x_754_ = 0;
v___x_755_ = l_Lean_Compiler_LCNF_Decl_internalize(v___x_748_, v___x_752_, v___x_753_, v___x_754_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
return v___x_755_;
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_del_object(v___x_745_);
lean_dec(v_inlineAttr_x3f_743_);
lean_dec_ref(v_toSignature_740_);
v_a_757_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_749_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_749_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___boxed(lean_object* v_decl_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj(v_decl_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_pushProj(lean_object* v_occurrence_777_){
_start:
{
lean_object* v___x_778_; uint8_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_778_ = ((lean_object*)(l_Lean_Compiler_LCNF_pushProj___closed__1));
v___x_779_ = 2;
v___x_780_ = ((lean_object*)(l_Lean_Compiler_LCNF_pushProj___closed__2));
v___x_781_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_778_, v___x_779_, v___x_780_, v_occurrence_777_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_852_; uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_852_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_));
v___x_853_ = 1;
v___x_854_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_));
v___x_855_ = l_Lean_registerTraceClass(v___x_852_, v___x_853_, v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2____boxed(lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_();
return v_res_857_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PushProj(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
