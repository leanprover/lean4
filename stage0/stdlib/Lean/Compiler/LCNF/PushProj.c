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
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_collectUsed(uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFVarIdHashSet;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_collectUsed(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__3;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_m_58_, lean_object* v_query_59_, lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
lean_object* v_zero_63_; uint8_t v_isZero_64_; 
v_zero_63_ = lean_unsigned_to_nat(0u);
v_isZero_64_ = lean_nat_dec_eq(v_x_61_, v_zero_63_);
if (v_isZero_64_ == 1)
{
lean_dec(v_x_62_);
lean_dec(v_x_61_);
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v___x_65_; 
v___x_65_ = lean_box(2);
return v___x_65_;
}
else
{
lean_object* v_val_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_73_; 
v_val_66_ = lean_ctor_get(v_x_60_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v_x_60_);
if (v_isSharedCheck_73_ == 0)
{
v___x_68_ = v_x_60_;
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_val_66_);
lean_dec(v_x_60_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
if (v_isShared_69_ == 0)
{
v___x_71_ = v___x_68_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_val_66_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
else
{
lean_object* v_keyArray_74_; lean_object* v_valueArray_75_; lean_object* v___x_76_; uint8_t v_isSome_77_; 
v_keyArray_74_ = lean_ctor_get(v_m_58_, 1);
v_valueArray_75_ = lean_ctor_get(v_m_58_, 2);
v___x_76_ = lean_array_fget_borrowed(v_keyArray_74_, v_x_62_);
v_isSome_77_ = lean_noption_is_some(v___x_76_);
if (v_isSome_77_ == 0)
{
lean_dec(v_x_61_);
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v___x_78_; 
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v_x_62_);
return v___x_78_;
}
else
{
lean_object* v_val_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
lean_dec(v_x_62_);
v_val_79_ = lean_ctor_get(v_x_60_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v_x_60_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v_x_60_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_val_79_);
lean_dec(v_x_60_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_val_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
else
{
lean_object* v_one_87_; lean_object* v_n_88_; lean_object* v___y_90_; 
v_one_87_ = lean_unsigned_to_nat(1u);
v_n_88_ = lean_nat_sub(v_x_61_, v_one_87_);
lean_dec(v_x_61_);
if (v_isSome_77_ == 0)
{
goto v___jp_96_;
}
else
{
lean_object* v___x_98_; uint8_t v_isSome_99_; 
v___x_98_ = lean_array_fget_borrowed(v_valueArray_75_, v_x_62_);
v_isSome_99_ = lean_noption_is_some(v___x_98_);
if (v_isSome_99_ == 0)
{
goto v___jp_96_;
}
else
{
lean_object* v_val_100_; uint8_t v___x_101_; 
lean_inc(v___x_76_);
v_val_100_ = lean_noption_get(v___x_76_);
v___x_101_ = l_Lean_instBEqFVarId_beq(v_val_100_, v_query_59_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
lean_dec(v_val_100_);
v___x_102_ = lean_array_get_size(v_keyArray_74_);
v___x_103_ = lean_nat_add(v_x_62_, v_one_87_);
lean_dec(v_x_62_);
v___x_104_ = lean_nat_dec_lt(v___x_103_, v___x_102_);
if (v___x_104_ == 0)
{
lean_dec(v___x_103_);
v_x_61_ = v_n_88_;
v_x_62_ = v_zero_63_;
goto _start;
}
else
{
v_x_61_ = v_n_88_;
v_x_62_ = v___x_103_;
goto _start;
}
}
else
{
lean_object* v_val_107_; lean_object* v___x_108_; 
lean_dec(v_n_88_);
lean_dec(v_x_60_);
lean_inc(v___x_98_);
v_val_107_ = lean_noption_get(v___x_98_);
v___x_108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_108_, 0, v_x_62_);
lean_ctor_set(v___x_108_, 1, v_val_100_);
lean_ctor_set(v___x_108_, 2, v_val_107_);
return v___x_108_;
}
}
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_91_ = lean_array_get_size(v_keyArray_74_);
v___x_92_ = lean_nat_add(v_x_62_, v_one_87_);
lean_dec(v_x_62_);
v___x_93_ = lean_nat_dec_lt(v___x_92_, v___x_91_);
if (v___x_93_ == 0)
{
lean_dec(v___x_92_);
v_x_60_ = v___y_90_;
v_x_61_ = v_n_88_;
v_x_62_ = v_zero_63_;
goto _start;
}
else
{
v_x_60_ = v___y_90_;
v_x_61_ = v_n_88_;
v_x_62_ = v___x_92_;
goto _start;
}
}
v___jp_96_:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v___x_97_; 
lean_inc(v_x_62_);
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v_x_62_);
v___y_90_ = v___x_97_;
goto v___jp_89_;
}
else
{
v___y_90_ = v_x_60_;
goto v___jp_89_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_109_, lean_object* v_query_110_, lean_object* v_x_111_, lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2_spec__5___redArg(v_m_109_, v_query_110_, v_x_111_, v_x_112_, v_x_113_);
lean_dec(v_query_110_);
lean_dec_ref(v_m_109_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2___redArg(lean_object* v_m_115_, lean_object* v_query_116_){
_start:
{
lean_object* v_keyArray_117_; lean_object* v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v_fold_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_keyArray_117_ = lean_ctor_get(v_m_115_, 1);
v___x_118_ = lean_array_get_size(v_keyArray_117_);
v___x_119_ = l_Lean_instHashableFVarId_hash(v_query_116_);
v___x_120_ = 32ULL;
v___x_121_ = lean_uint64_shift_right(v___x_119_, v___x_120_);
v_fold_122_ = lean_uint64_xor(v___x_119_, v___x_121_);
v___x_123_ = 16ULL;
v___x_124_ = lean_uint64_shift_right(v_fold_122_, v___x_123_);
v___x_125_ = lean_uint64_xor(v_fold_122_, v___x_124_);
v___x_126_ = lean_uint64_to_usize(v___x_125_);
v___x_127_ = lean_usize_of_nat(v___x_118_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_sub(v___x_127_, v___x_128_);
v___x_130_ = lean_usize_land(v___x_126_, v___x_129_);
v___x_131_ = lean_usize_to_nat(v___x_130_);
v___x_132_ = lean_box(0);
v___x_133_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2_spec__5___redArg(v_m_115_, v_query_116_, v___x_132_, v___x_118_, v___x_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_134_, lean_object* v_query_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2___redArg(v_m_134_, v_query_135_);
lean_dec(v_query_135_);
lean_dec_ref(v_m_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(lean_object* v_m_137_, lean_object* v_query_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2___redArg(v_m_137_, v_query_138_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_index_140_; lean_object* v_key_141_; lean_object* v_value_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_index_140_ = lean_ctor_get(v___x_139_, 0);
v_key_141_ = lean_ctor_get(v___x_139_, 1);
v_value_142_ = lean_ctor_get(v___x_139_, 2);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_139_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_value_142_);
lean_inc(v_key_141_);
lean_inc(v_index_140_);
lean_dec(v___x_139_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_index_140_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_key_141_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_value_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
else
{
lean_object* v___x_150_; 
lean_dec(v___x_139_);
v___x_150_ = lean_box(1);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg___boxed(lean_object* v_m_151_, lean_object* v_query_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_m_151_, v_query_152_);
lean_dec(v_query_152_);
lean_dec_ref(v_m_151_);
return v_res_153_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(lean_object* v_m_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_m_154_, v_a_155_);
if (lean_obj_tag(v___x_156_) == 0)
{
uint8_t v___x_157_; 
lean_dec_ref_known(v___x_156_, 3);
v___x_157_ = 1;
return v___x_157_;
}
else
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg___boxed(lean_object* v_m_159_, lean_object* v_a_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_m_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_m_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0(lean_object* v_altsUsed_163_, lean_object* v___x_164_, lean_object* v_fvar_165_, lean_object* v_b_166_, uint8_t v___x_167_, lean_object* v_k_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_174_ = l_Lean_instInhabitedFVarIdHashSet;
v___x_175_ = lean_array_get_borrowed(v___x_174_, v_altsUsed_163_, v___x_164_);
v___x_176_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v___x_175_, v_fvar_165_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
lean_dec_ref(v_b_166_);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v_k_168_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_mk_empty_array_with_capacity(v___x_178_);
v___x_180_ = lean_array_push(v___x_179_, v_b_166_);
v___x_181_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_167_, v___x_180_, v_k_168_);
lean_dec_ref(v___x_180_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0___boxed(lean_object* v_altsUsed_183_, lean_object* v___x_184_, lean_object* v_fvar_185_, lean_object* v_b_186_, lean_object* v___x_187_, lean_object* v_k_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
uint8_t v___x_2625__boxed_194_; lean_object* v_res_195_; 
v___x_2625__boxed_194_ = lean_unbox(v___x_187_);
v_res_195_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0(v_altsUsed_183_, v___x_184_, v_fvar_185_, v_b_186_, v___x_2625__boxed_194_, v_k_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v_fvar_185_);
lean_dec(v___x_184_);
lean_dec_ref(v_altsUsed_183_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(lean_object* v_altsUsed_196_, lean_object* v_fvar_197_, lean_object* v_b_198_, size_t v_sz_199_, size_t v_i_200_, lean_object* v_bs_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
uint8_t v___x_207_; 
v___x_207_ = lean_usize_dec_lt(v_i_200_, v_sz_199_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
lean_dec_ref(v_b_198_);
lean_dec(v_fvar_197_);
lean_dec_ref(v_altsUsed_196_);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v_bs_201_);
return v___x_208_;
}
else
{
uint8_t v___x_209_; lean_object* v_v_210_; lean_object* v___x_211_; lean_object* v_bs_x27_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___f_215_; lean_object* v___x_216_; 
v___x_209_ = 1;
v_v_210_ = lean_array_uget(v_bs_201_, v_i_200_);
v___x_211_ = lean_unsigned_to_nat(0u);
v_bs_x27_212_ = lean_array_uset(v_bs_201_, v_i_200_, v___x_211_);
v___x_213_ = lean_usize_to_nat(v_i_200_);
v___x_214_ = lean_box(v___x_209_);
lean_inc_ref(v_b_198_);
lean_inc(v_fvar_197_);
lean_inc_ref(v_altsUsed_196_);
v___f_215_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_215_, 0, v_altsUsed_196_);
lean_closure_set(v___f_215_, 1, v___x_213_);
lean_closure_set(v___f_215_, 2, v_fvar_197_);
lean_closure_set(v___f_215_, 3, v_b_198_);
lean_closure_set(v___f_215_, 4, v___x_214_);
v___x_216_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v_v_210_, v___f_215_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref_known(v___x_216_, 1);
v___x_218_ = ((size_t)1ULL);
v___x_219_ = lean_usize_add(v_i_200_, v___x_218_);
v___x_220_ = lean_array_uset(v_bs_x27_212_, v_i_200_, v_a_217_);
v_i_200_ = v___x_219_;
v_bs_201_ = v___x_220_;
goto _start;
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v_bs_x27_212_);
lean_dec_ref(v_b_198_);
lean_dec(v_fvar_197_);
lean_dec_ref(v_altsUsed_196_);
v_a_222_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_216_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_216_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___boxed(lean_object* v_altsUsed_230_, lean_object* v_fvar_231_, lean_object* v_b_232_, lean_object* v_sz_233_, lean_object* v_i_234_, lean_object* v_bs_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
size_t v_sz_boxed_241_; size_t v_i_boxed_242_; lean_object* v_res_243_; 
v_sz_boxed_241_ = lean_unbox_usize(v_sz_233_);
lean_dec(v_sz_233_);
v_i_boxed_242_ = lean_unbox_usize(v_i_234_);
lean_dec(v_i_234_);
v_res_243_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_230_, v_fvar_231_, v_b_232_, v_sz_boxed_241_, v_i_boxed_242_, v_bs_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(lean_object* v_fvar_244_, lean_object* v_b_245_, size_t v_sz_246_, size_t v_i_247_, lean_object* v_bs_248_){
_start:
{
uint8_t v___x_249_; 
v___x_249_ = lean_usize_dec_lt(v_i_247_, v_sz_246_);
if (v___x_249_ == 0)
{
lean_dec_ref(v_b_245_);
return v_bs_248_;
}
else
{
lean_object* v_v_250_; lean_object* v___x_251_; lean_object* v_bs_x27_252_; lean_object* v___y_254_; uint8_t v___x_259_; 
v_v_250_ = lean_array_uget(v_bs_248_, v_i_247_);
v___x_251_ = lean_unsigned_to_nat(0u);
v_bs_x27_252_ = lean_array_uset(v_bs_248_, v_i_247_, v___x_251_);
v___x_259_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_v_250_, v_fvar_244_);
if (v___x_259_ == 0)
{
v___y_254_ = v_v_250_;
goto v___jp_253_;
}
else
{
uint8_t v___x_260_; lean_object* v___x_261_; 
v___x_260_ = 1;
lean_inc_ref(v_b_245_);
v___x_261_ = l_Lean_Compiler_LCNF_CodeDecl_collectUsed(v___x_260_, v_b_245_, v_v_250_);
v___y_254_ = v___x_261_;
goto v___jp_253_;
}
v___jp_253_:
{
size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; 
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_add(v_i_247_, v___x_255_);
v___x_257_ = lean_array_uset(v_bs_x27_252_, v_i_247_, v___y_254_);
v_i_247_ = v___x_256_;
v_bs_248_ = v___x_257_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3___boxed(lean_object* v_fvar_262_, lean_object* v_b_263_, lean_object* v_sz_264_, lean_object* v_i_265_, lean_object* v_bs_266_){
_start:
{
size_t v_sz_boxed_267_; size_t v_i_boxed_268_; lean_object* v_res_269_; 
v_sz_boxed_267_ = lean_unbox_usize(v_sz_264_);
lean_dec(v_sz_264_);
v_i_boxed_268_ = lean_unbox_usize(v_i_265_);
lean_dec(v_i_265_);
v_res_269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(v_fvar_262_, v_b_263_, v_sz_boxed_267_, v_i_boxed_268_, v_bs_266_);
lean_dec(v_fvar_262_);
return v_res_269_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0(void){
_start:
{
uint8_t v___x_270_; lean_object* v___x_271_; 
v___x_270_ = 1;
v___x_271_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(lean_object* v_decls_272_, lean_object* v_alts_273_, lean_object* v_altsUsed_274_, lean_object* v_ctx_275_, lean_object* v_ctxUsed_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_282_ = lean_array_get_size(v_decls_272_);
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_nat_dec_eq(v___x_282_, v___x_283_);
if (v___x_284_ == 0)
{
uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_b_289_; lean_object* v_bs_290_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_285_ = 1;
v___x_286_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0);
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_sub(v___x_282_, v___x_287_);
v_b_289_ = lean_array_get(v___x_286_, v_decls_272_, v___x_288_);
lean_dec(v___x_288_);
v_bs_290_ = lean_array_pop(v_decls_272_);
lean_inc(v_b_289_);
lean_inc_ref(v_bs_290_);
v___x_312_ = lean_array_push(v_bs_290_, v_b_289_);
lean_inc_ref(v_ctx_275_);
v___x_313_ = l_Array_reverse___redArg(v_ctx_275_);
v___x_314_ = l_Array_append___redArg(v___x_312_, v___x_313_);
lean_dec_ref(v___x_313_);
lean_inc_ref(v_alts_273_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v_alts_273_);
if (lean_obj_tag(v_b_289_) == 0)
{
lean_object* v_decl_316_; lean_object* v_fvarId_317_; lean_object* v_value_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_fvar_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; 
v_decl_316_ = lean_ctor_get(v_b_289_, 0);
v_fvarId_317_ = lean_ctor_get(v_decl_316_, 0);
v_value_318_ = lean_ctor_get(v_decl_316_, 3);
lean_inc_ref_n(v_b_289_, 2);
lean_inc_ref(v_ctx_275_);
v___x_319_ = lean_array_push(v_ctx_275_, v_b_289_);
lean_inc_ref(v_ctxUsed_276_);
v___x_320_ = l_Lean_Compiler_LCNF_CodeDecl_collectUsed(v___x_285_, v_b_289_, v_ctxUsed_276_);
switch(lean_obj_tag(v_value_318_))
{
case 7:
{
lean_dec_ref_known(v___x_315_, 2);
lean_inc(v_fvarId_317_);
v_fvar_322_ = v_fvarId_317_;
v___y_323_ = v_a_277_;
v___y_324_ = v_a_278_;
v___y_325_ = v_a_279_;
v___y_326_ = v_a_280_;
goto v___jp_321_;
}
case 6:
{
lean_dec_ref_known(v___x_315_, 2);
lean_inc(v_fvarId_317_);
v_fvar_322_ = v_fvarId_317_;
v___y_323_ = v_a_277_;
v___y_324_ = v_a_278_;
v___y_325_ = v_a_279_;
v___y_326_ = v_a_280_;
goto v___jp_321_;
}
case 8:
{
lean_dec_ref_known(v___x_315_, 2);
lean_inc(v_fvarId_317_);
v_fvar_322_ = v_fvarId_317_;
v___y_323_ = v_a_277_;
v___y_324_ = v_a_278_;
v___y_325_ = v_a_279_;
v___y_326_ = v_a_280_;
goto v___jp_321_;
}
default: 
{
lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v___x_320_);
lean_dec_ref(v___x_319_);
lean_dec_ref(v_bs_290_);
lean_dec_ref(v_ctxUsed_276_);
lean_dec_ref(v_ctx_275_);
lean_dec_ref(v_altsUsed_274_);
lean_dec_ref(v_alts_273_);
v_isSharedCheck_335_ = !lean_is_exclusive(v_b_289_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v_b_289_, 0);
lean_dec(v_unused_336_);
v___x_330_ = v_b_289_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_dec(v_b_289_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_315_);
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_315_);
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
v___jp_321_:
{
uint8_t v___x_327_; 
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_ctxUsed_276_, v_fvar_322_);
if (v___x_327_ == 0)
{
lean_dec_ref(v___x_320_);
lean_dec_ref(v___x_319_);
v___y_292_ = v___y_325_;
v___y_293_ = v___y_326_;
v___y_294_ = v_fvar_322_;
v___y_295_ = v___y_324_;
v___y_296_ = v___y_323_;
goto v___jp_291_;
}
else
{
if (v___x_284_ == 0)
{
lean_dec(v_fvar_322_);
lean_dec_ref_known(v_b_289_, 1);
lean_dec_ref(v_ctxUsed_276_);
lean_dec_ref(v_ctx_275_);
v_decls_272_ = v_bs_290_;
v_ctx_275_ = v___x_319_;
v_ctxUsed_276_ = v___x_320_;
v_a_277_ = v___y_323_;
v_a_278_ = v___y_324_;
v_a_279_ = v___y_325_;
v_a_280_ = v___y_326_;
goto _start;
}
else
{
lean_dec_ref(v___x_320_);
lean_dec_ref(v___x_319_);
v___y_292_ = v___y_325_;
v___y_293_ = v___y_326_;
v___y_294_ = v_fvar_322_;
v___y_295_ = v___y_324_;
v___y_296_ = v___y_323_;
goto v___jp_291_;
}
}
}
}
else
{
lean_object* v___x_337_; 
lean_dec_ref(v_bs_290_);
lean_dec(v_b_289_);
lean_dec_ref(v_ctxUsed_276_);
lean_dec_ref(v_ctx_275_);
lean_dec_ref(v_altsUsed_274_);
lean_dec_ref(v_alts_273_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_315_);
return v___x_337_;
}
v___jp_291_:
{
size_t v_sz_297_; size_t v___x_298_; lean_object* v___x_299_; 
v_sz_297_ = lean_array_size(v_alts_273_);
v___x_298_ = ((size_t)0ULL);
lean_inc(v_b_289_);
lean_inc(v___y_294_);
lean_inc_ref(v_altsUsed_274_);
v___x_299_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_274_, v___y_294_, v_b_289_, v_sz_297_, v___x_298_, v_alts_273_, v___y_296_, v___y_295_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; size_t v_sz_301_; lean_object* v___x_302_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref_known(v___x_299_, 1);
v_sz_301_ = lean_array_size(v_altsUsed_274_);
v___x_302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(v___y_294_, v_b_289_, v_sz_301_, v___x_298_, v_altsUsed_274_);
lean_dec(v___y_294_);
v_decls_272_ = v_bs_290_;
v_alts_273_ = v_a_300_;
v_altsUsed_274_ = v___x_302_;
v_a_277_ = v___y_296_;
v_a_278_ = v___y_295_;
v_a_279_ = v___y_292_;
v_a_280_ = v___y_293_;
goto _start;
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec(v___y_294_);
lean_dec_ref(v_bs_290_);
lean_dec(v_b_289_);
lean_dec_ref(v_ctxUsed_276_);
lean_dec_ref(v_ctx_275_);
lean_dec_ref(v_altsUsed_274_);
v_a_304_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_299_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_299_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec_ref(v_ctxUsed_276_);
lean_dec_ref(v_altsUsed_274_);
lean_dec_ref(v_decls_272_);
v___x_338_ = l_Array_reverse___redArg(v_ctx_275_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v_alts_273_);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___boxed(lean_object* v_decls_341_, lean_object* v_alts_342_, lean_object* v_altsUsed_343_, lean_object* v_ctx_344_, lean_object* v_ctxUsed_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(v_decls_341_, v_alts_342_, v_altsUsed_343_, v_ctx_344_, v_ctxUsed_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
return v_res_351_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0(lean_object* v_00_u03b2_352_, lean_object* v_m_353_, lean_object* v_a_354_){
_start:
{
uint8_t v___x_355_; 
v___x_355_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_m_353_, v_a_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___boxed(lean_object* v_00_u03b2_356_, lean_object* v_m_357_, lean_object* v_a_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0(v_00_u03b2_356_, v_m_357_, v_a_358_);
lean_dec(v_a_358_);
lean_dec_ref(v_m_357_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2(lean_object* v_altsUsed_361_, lean_object* v_fvar_362_, lean_object* v_b_363_, lean_object* v_as_364_, size_t v_sz_365_, size_t v_i_366_, lean_object* v_bs_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_361_, v_fvar_362_, v_b_363_, v_sz_365_, v_i_366_, v_bs_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___boxed(lean_object* v_altsUsed_374_, lean_object* v_fvar_375_, lean_object* v_b_376_, lean_object* v_as_377_, lean_object* v_sz_378_, lean_object* v_i_379_, lean_object* v_bs_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
size_t v_sz_boxed_386_; size_t v_i_boxed_387_; lean_object* v_res_388_; 
v_sz_boxed_386_ = lean_unbox_usize(v_sz_378_);
lean_dec(v_sz_378_);
v_i_boxed_387_ = lean_unbox_usize(v_i_379_);
lean_dec(v_i_379_);
v_res_388_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2(v_altsUsed_374_, v_fvar_375_, v_b_376_, v_as_377_, v_sz_boxed_386_, v_i_boxed_387_, v_bs_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec_ref(v_as_377_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0(lean_object* v_00_u03b2_389_, lean_object* v_m_390_, lean_object* v_query_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_m_390_, v_query_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_393_, lean_object* v_m_394_, lean_object* v_query_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0(v_00_u03b2_393_, v_m_394_, v_query_395_);
lean_dec(v_query_395_);
lean_dec_ref(v_m_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_397_, lean_object* v_m_398_, lean_object* v_query_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2___redArg(v_m_398_, v_query_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_401_, lean_object* v_m_402_, lean_object* v_query_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2(v_00_u03b2_401_, v_m_402_, v_query_403_);
lean_dec(v_query_403_);
lean_dec_ref(v_m_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_405_, lean_object* v_m_406_, lean_object* v_query_407_, lean_object* v_x_408_, lean_object* v_x_409_, lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2_spec__5___redArg(v_m_406_, v_query_407_, v_x_408_, v_x_409_, v_x_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_413_, lean_object* v_m_414_, lean_object* v_query_415_, lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_413_, v_m_414_, v_query_415_, v_x_416_, v_x_417_, v_x_418_, v_x_419_);
lean_dec(v_query_415_);
lean_dec_ref(v_m_414_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4_spec__5___redArg(lean_object* v_b_421_, lean_object* v_acc_422_, lean_object* v_i_423_){
_start:
{
lean_object* v___y_425_; lean_object* v_keyArray_433_; lean_object* v_valueArray_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_keyArray_433_ = lean_ctor_get(v_b_421_, 1);
v_valueArray_434_ = lean_ctor_get(v_b_421_, 2);
v___x_435_ = lean_array_get_size(v_keyArray_433_);
v___x_436_ = lean_nat_dec_lt(v_i_423_, v___x_435_);
if (v___x_436_ == 0)
{
lean_dec(v_i_423_);
return v_acc_422_;
}
else
{
lean_object* v___x_437_; uint8_t v_isSome_438_; 
v___x_437_ = lean_array_fget_borrowed(v_keyArray_433_, v_i_423_);
v_isSome_438_ = lean_noption_is_some(v___x_437_);
if (v_isSome_438_ == 0)
{
goto v___jp_429_;
}
else
{
lean_object* v___x_439_; uint8_t v_isSome_440_; 
v___x_439_ = lean_array_fget_borrowed(v_valueArray_434_, v_i_423_);
v_isSome_440_ = lean_noption_is_some(v___x_439_);
if (v_isSome_440_ == 0)
{
goto v___jp_429_;
}
else
{
lean_object* v_val_441_; lean_object* v_val_442_; lean_object* v_i_444_; lean_object* v___x_449_; 
lean_inc(v___x_437_);
v_val_441_ = lean_noption_get(v___x_437_);
lean_inc(v___x_439_);
v_val_442_ = lean_noption_get(v___x_439_);
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2___redArg(v_acc_422_, v_val_441_);
switch(lean_obj_tag(v___x_449_))
{
case 0:
{
lean_object* v_index_450_; lean_object* v_size_451_; lean_object* v___x_452_; 
v_index_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_index_450_);
lean_dec_ref_known(v___x_449_, 3);
v_size_451_ = lean_ctor_get(v_acc_422_, 0);
lean_inc(v_size_451_);
v___x_452_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_422_, v_size_451_, v_index_450_, v_val_441_, v_val_442_);
lean_dec(v_index_450_);
v___y_425_ = v___x_452_;
goto v___jp_424_;
}
case 1:
{
lean_object* v_index_453_; 
v_index_453_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_index_453_);
lean_dec_ref_known(v___x_449_, 1);
v_i_444_ = v_index_453_;
goto v___jp_443_;
}
default: 
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_422_, v___x_454_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_index_456_; 
v_index_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_index_456_);
lean_dec_ref_known(v___x_455_, 1);
v_i_444_ = v_index_456_;
goto v___jp_443_;
}
else
{
lean_dec(v_val_442_);
lean_dec(v_val_441_);
v___y_425_ = v_acc_422_;
goto v___jp_424_;
}
}
}
v___jp_443_:
{
lean_object* v_size_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_size_445_ = lean_ctor_get(v_acc_422_, 0);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v_size_445_, v___x_446_);
v___x_448_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_422_, v___x_447_, v_i_444_, v_val_441_, v_val_442_);
lean_dec(v_i_444_);
v___y_425_ = v___x_448_;
goto v___jp_424_;
}
}
}
}
v___jp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_nat_add(v_i_423_, v___x_426_);
lean_dec(v_i_423_);
v_acc_422_ = v___y_425_;
v_i_423_ = v___x_427_;
goto _start;
}
v___jp_429_:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = lean_nat_add(v_i_423_, v___x_430_);
lean_dec(v_i_423_);
v_i_423_ = v___x_431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_b_457_, lean_object* v_acc_458_, lean_object* v_i_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4_spec__5___redArg(v_b_457_, v_acc_458_, v_i_459_);
lean_dec_ref(v_b_457_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4___redArg(lean_object* v_init_461_, lean_object* v_b_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4_spec__5___redArg(v_b_462_, v_init_461_, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4___redArg___boxed(lean_object* v_init_465_, lean_object* v_b_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4___redArg(v_init_465_, v_b_466_);
lean_dec_ref(v_b_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___redArg(lean_object* v_m_468_){
_start:
{
lean_object* v_keyArray_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_cellCount_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_target_476_; lean_object* v___x_477_; 
v_keyArray_469_ = lean_ctor_get(v_m_468_, 1);
v___x_470_ = lean_array_get_size(v_keyArray_469_);
v___x_471_ = lean_unsigned_to_nat(2u);
v_cellCount_472_ = lean_nat_mul(v___x_470_, v___x_471_);
v___x_473_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_472_);
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_472_);
v___x_475_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_472_);
v_target_476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_476_, 0, v___x_473_);
lean_ctor_set(v_target_476_, 1, v___x_474_);
lean_ctor_set(v_target_476_, 2, v___x_475_);
v___x_477_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4___redArg(v_target_476_, v_m_468_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___redArg___boxed(lean_object* v_m_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___redArg(v_m_478_);
lean_dec_ref(v_m_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(size_t v_sz_480_, size_t v_i_481_, lean_object* v_bs_482_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_lt(v_i_481_, v_sz_480_);
if (v___x_483_ == 0)
{
return v_bs_482_;
}
else
{
lean_object* v___x_484_; lean_object* v_v_485_; lean_object* v___x_486_; lean_object* v_bs_x27_487_; uint8_t v___x_488_; lean_object* v___y_490_; 
v___x_484_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v_v_485_ = lean_array_uget(v_bs_482_, v_i_481_);
v___x_486_ = lean_unsigned_to_nat(0u);
v_bs_x27_487_ = lean_array_uset(v_bs_482_, v_i_481_, v___x_486_);
v___x_488_ = 1;
switch(lean_obj_tag(v_v_485_))
{
case 0:
{
lean_object* v_code_496_; 
v_code_496_ = lean_ctor_get(v_v_485_, 2);
lean_inc_ref(v_code_496_);
lean_dec_ref_known(v_v_485_, 3);
v___y_490_ = v_code_496_;
goto v___jp_489_;
}
case 1:
{
lean_object* v_code_497_; 
v_code_497_ = lean_ctor_get(v_v_485_, 1);
lean_inc_ref(v_code_497_);
lean_dec_ref_known(v_v_485_, 2);
v___y_490_ = v_code_497_;
goto v___jp_489_;
}
default: 
{
lean_object* v_code_498_; 
v_code_498_ = lean_ctor_get(v_v_485_, 0);
lean_inc_ref(v_code_498_);
lean_dec_ref_known(v_v_485_, 1);
v___y_490_ = v_code_498_;
goto v___jp_489_;
}
}
v___jp_489_:
{
lean_object* v___x_491_; size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v___x_491_ = l_Lean_Compiler_LCNF_Code_collectUsed(v___x_488_, v___y_490_, v___x_484_);
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_481_, v___x_492_);
v___x_494_ = lean_array_uset(v_bs_x27_487_, v_i_481_, v___x_491_);
v_i_481_ = v___x_493_;
v_bs_482_ = v___x_494_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1___boxed(lean_object* v_sz_499_, lean_object* v_i_500_, lean_object* v_bs_501_){
_start:
{
size_t v_sz_boxed_502_; size_t v_i_boxed_503_; lean_object* v_res_504_; 
v_sz_boxed_502_ = lean_unbox_usize(v_sz_499_);
lean_dec(v_sz_499_);
v_i_boxed_503_ = lean_unbox_usize(v_i_500_);
lean_dec(v_i_500_);
v_res_504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(v_sz_boxed_502_, v_i_boxed_503_, v_bs_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed(lean_object* v_code_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(v_code_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2(lean_object* v_i_514_, lean_object* v_as_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_array_get_size(v_as_515_);
v___x_522_ = lean_nat_dec_lt(v_i_514_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_dec(v_i_514_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v_as_515_);
return v___x_523_;
}
else
{
lean_object* v_a_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_a_524_ = lean_array_fget_borrowed(v_as_515_, v_i_514_);
v___x_525_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed), 6, 0);
lean_inc(v_a_524_);
v___x_526_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v_a_524_, v___x_525_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; size_t v___x_528_; size_t v___x_529_; uint8_t v___x_530_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = lean_ptr_addr(v_a_524_);
v___x_529_ = lean_ptr_addr(v_a_527_);
v___x_530_ = lean_usize_dec_eq(v___x_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_add(v_i_514_, v___x_531_);
v___x_533_ = lean_array_fset(v_as_515_, v_i_514_, v_a_527_);
lean_dec(v_i_514_);
v_i_514_ = v___x_532_;
v_as_515_ = v___x_533_;
goto _start;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v_a_527_);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_i_514_, v___x_535_);
lean_dec(v_i_514_);
v_i_514_ = v___x_536_;
goto _start;
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v_as_515_);
lean_dec(v_i_514_);
v_a_538_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_526_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_526_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
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
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_547_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___redArg(v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__1(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0);
v___x_550_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_549_, v___x_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(lean_object* v_c_551_, lean_object* v_decls_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_typeName_558_; lean_object* v_resultType_559_; lean_object* v_discr_560_; lean_object* v_alts_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_669_; 
v_typeName_558_ = lean_ctor_get(v_c_551_, 0);
v_resultType_559_ = lean_ctor_get(v_c_551_, 1);
v_discr_560_ = lean_ctor_get(v_c_551_, 2);
v_alts_561_ = lean_ctor_get(v_c_551_, 3);
v_isSharedCheck_669_ = !lean_is_exclusive(v_c_551_);
if (v_isSharedCheck_669_ == 0)
{
v___x_563_ = v_c_551_;
v_isShared_564_ = v_isSharedCheck_669_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_alts_561_);
lean_inc(v_discr_560_);
lean_inc(v_resultType_559_);
lean_inc(v_typeName_558_);
lean_dec(v_c_551_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_669_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; uint8_t v___x_566_; size_t v_sz_567_; size_t v___x_568_; lean_object* v_altsUsed_569_; lean_object* v___y_571_; lean_object* v___x_608_; lean_object* v___y_610_; lean_object* v_i_611_; lean_object* v___y_617_; lean_object* v___y_627_; lean_object* v_i_628_; lean_object* v___x_642_; 
v___x_565_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_566_ = 1;
v_sz_567_ = lean_array_size(v_alts_561_);
v___x_568_ = ((size_t)0ULL);
lean_inc_ref(v_alts_561_);
v_altsUsed_569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(v_sz_567_, v___x_568_, v_alts_561_);
v___x_608_ = lean_box(0);
v___x_642_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2___redArg(v___x_565_, v_discr_560_);
switch(lean_obj_tag(v___x_642_))
{
case 0:
{
lean_dec_ref_known(v___x_642_, 3);
v___y_571_ = v___x_565_;
goto v___jp_570_;
}
case 1:
{
lean_object* v_index_643_; lean_object* v_size_644_; lean_object* v_keyArray_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_index_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_index_643_);
lean_dec_ref_known(v___x_642_, 1);
v_size_644_ = lean_ctor_get(v___x_565_, 0);
v_keyArray_645_ = lean_ctor_get(v___x_565_, 1);
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_add(v_size_644_, v___x_646_);
v___x_648_ = lean_array_get_size(v_keyArray_645_);
v___x_649_ = lean_nat_dec_lt(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
lean_dec(v___x_647_);
lean_dec(v_index_643_);
goto v___jp_633_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_650_ = lean_unsigned_to_nat(4u);
v___x_651_ = lean_nat_mul(v___x_647_, v___x_650_);
v___x_652_ = lean_unsigned_to_nat(3u);
v___x_653_ = lean_nat_mul(v___x_648_, v___x_652_);
v___x_654_ = lean_nat_dec_le(v___x_651_, v___x_653_);
lean_dec(v___x_653_);
lean_dec(v___x_651_);
if (v___x_654_ == 0)
{
lean_dec(v___x_647_);
lean_dec(v_index_643_);
goto v___jp_633_;
}
else
{
lean_object* v___x_655_; 
lean_inc(v_discr_560_);
v___x_655_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_565_, v___x_647_, v_index_643_, v_discr_560_, v___x_608_);
lean_dec(v_index_643_);
v___y_571_ = v___x_655_;
goto v___jp_570_;
}
}
}
default: 
{
lean_object* v_size_656_; lean_object* v_keyArray_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v_size_656_ = lean_ctor_get(v___x_565_, 0);
v_keyArray_657_ = lean_ctor_get(v___x_565_, 1);
v___x_658_ = lean_unsigned_to_nat(1u);
v___x_659_ = lean_nat_add(v_size_656_, v___x_658_);
v___x_660_ = lean_array_get_size(v_keyArray_657_);
v___x_661_ = lean_nat_dec_lt(v___x_659_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
lean_dec(v___x_659_);
v___x_662_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0);
v___y_617_ = v___x_662_;
goto v___jp_616_;
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_663_ = lean_unsigned_to_nat(4u);
v___x_664_ = lean_nat_mul(v___x_659_, v___x_663_);
lean_dec(v___x_659_);
v___x_665_ = lean_unsigned_to_nat(3u);
v___x_666_ = lean_nat_mul(v___x_660_, v___x_665_);
v___x_667_ = lean_nat_dec_le(v___x_664_, v___x_666_);
lean_dec(v___x_666_);
lean_dec(v___x_664_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
v___x_668_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0);
v___y_617_ = v___x_668_;
goto v___jp_616_;
}
else
{
v___y_617_ = v___x_565_;
goto v___jp_616_;
}
}
}
}
v___jp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0));
v___x_574_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(v_decls_552_, v_alts_561_, v_altsUsed_569_, v___x_573_, v___y_571_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_578_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v_fst_576_ = lean_ctor_get(v_a_575_, 0);
lean_inc(v_fst_576_);
v_snd_577_ = lean_ctor_get(v_a_575_, 1);
lean_inc(v_snd_577_);
lean_dec(v_a_575_);
v___x_578_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2(v___x_572_, v_snd_577_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_591_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_591_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_591_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_591_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 3, v_a_579_);
v___x_584_ = v___x_563_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_typeName_558_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_resultType_559_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_discr_560_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v_a_579_);
v___x_584_ = v_reuseFailAlloc_590_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_585_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
v___x_586_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_566_, v_fst_576_, v___x_585_);
lean_dec(v_fst_576_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_586_);
v___x_588_ = v___x_581_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_fst_576_);
lean_del_object(v___x_563_);
lean_dec(v_discr_560_);
lean_dec_ref(v_resultType_559_);
lean_dec(v_typeName_558_);
v_a_592_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_578_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_578_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_del_object(v___x_563_);
lean_dec(v_discr_560_);
lean_dec_ref(v_resultType_559_);
lean_dec(v_typeName_558_);
v_a_600_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_574_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_574_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
v___jp_609_:
{
lean_object* v_size_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_size_612_ = lean_ctor_get(v___y_610_, 0);
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_add(v_size_612_, v___x_613_);
lean_inc(v_discr_560_);
v___x_615_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_610_, v___x_614_, v_i_611_, v_discr_560_, v___x_608_);
lean_dec(v_i_611_);
v___y_571_ = v___x_615_;
goto v___jp_570_;
}
v___jp_616_:
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2___redArg(v___y_617_, v_discr_560_);
switch(lean_obj_tag(v___x_618_))
{
case 0:
{
lean_object* v_index_619_; lean_object* v_size_620_; lean_object* v___x_621_; 
v_index_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_index_619_);
lean_dec_ref_known(v___x_618_, 3);
v_size_620_ = lean_ctor_get(v___y_617_, 0);
lean_inc(v_size_620_);
lean_inc(v_discr_560_);
v___x_621_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_617_, v_size_620_, v_index_619_, v_discr_560_, v___x_608_);
lean_dec(v_index_619_);
v___y_571_ = v___x_621_;
goto v___jp_570_;
}
case 1:
{
lean_object* v_index_622_; 
v_index_622_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_index_622_);
lean_dec_ref_known(v___x_618_, 1);
v___y_610_ = v___y_617_;
v_i_611_ = v_index_622_;
goto v___jp_609_;
}
default: 
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_617_, v___x_623_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_index_625_; 
v_index_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_index_625_);
lean_dec_ref_known(v___x_624_, 1);
v___y_610_ = v___y_617_;
v_i_611_ = v_index_625_;
goto v___jp_609_;
}
else
{
v___y_571_ = v___y_617_;
goto v___jp_570_;
}
}
}
}
v___jp_626_:
{
lean_object* v_size_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_size_629_ = lean_ctor_get(v___y_627_, 0);
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_add(v_size_629_, v___x_630_);
lean_inc(v_discr_560_);
v___x_632_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_627_, v___x_631_, v_i_628_, v_discr_560_, v___x_608_);
lean_dec(v_i_628_);
v___y_571_ = v___x_632_;
goto v___jp_570_;
}
v___jp_633_:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__0);
v___x_635_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0_spec__2___redArg(v___x_634_, v_discr_560_);
switch(lean_obj_tag(v___x_635_))
{
case 0:
{
lean_object* v_index_636_; lean_object* v_size_637_; lean_object* v___x_638_; 
v_index_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_index_636_);
lean_dec_ref_known(v___x_635_, 3);
v_size_637_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_discr_560_);
lean_inc(v_size_637_);
v___x_638_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_634_, v_size_637_, v_index_636_, v_discr_560_, v___x_608_);
lean_dec(v_index_636_);
v___y_571_ = v___x_638_;
goto v___jp_570_;
}
case 1:
{
lean_object* v_index_639_; 
v_index_639_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_index_639_);
lean_dec_ref_known(v___x_635_, 1);
v___y_627_ = v___x_634_;
v_i_628_ = v_index_639_;
goto v___jp_626_;
}
default: 
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__1, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__1_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___closed__1);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_index_641_; 
v_index_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_index_641_);
v___y_627_ = v___x_634_;
v_i_628_ = v_index_641_;
goto v___jp_626_;
}
else
{
v___y_571_ = v___x_634_;
goto v___jp_570_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(lean_object* v_c_670_, lean_object* v_decls_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
switch(lean_obj_tag(v_c_670_))
{
case 0:
{
lean_object* v_decl_677_; lean_object* v_k_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_decl_677_ = lean_ctor_get(v_c_670_, 0);
lean_inc_ref(v_decl_677_);
v_k_678_ = lean_ctor_get(v_c_670_, 1);
lean_inc_ref(v_k_678_);
lean_dec_ref_known(v_c_670_, 2);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v_decl_677_);
v___x_680_ = lean_array_push(v_decls_671_, v___x_679_);
v_c_670_ = v_k_678_;
v_decls_671_ = v___x_680_;
goto _start;
}
case 2:
{
lean_object* v_decl_682_; lean_object* v_k_683_; lean_object* v_params_684_; lean_object* v_type_685_; lean_object* v_value_686_; lean_object* v___x_687_; 
v_decl_682_ = lean_ctor_get(v_c_670_, 0);
lean_inc_ref(v_decl_682_);
v_k_683_ = lean_ctor_get(v_c_670_, 1);
lean_inc_ref(v_k_683_);
lean_dec_ref_known(v_c_670_, 2);
v_params_684_ = lean_ctor_get(v_decl_682_, 2);
lean_inc_ref(v_params_684_);
v_type_685_ = lean_ctor_get(v_decl_682_, 3);
lean_inc_ref(v_type_685_);
v_value_686_ = lean_ctor_get(v_decl_682_, 4);
lean_inc_ref(v_value_686_);
v___x_687_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(v_value_686_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_708_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_708_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_708_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_708_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
uint8_t v___x_692_; lean_object* v___x_693_; 
v___x_692_ = 1;
v___x_693_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_692_, v_decl_682_, v_type_685_, v_params_684_, v_a_688_, v_a_673_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
if (v_isShared_691_ == 0)
{
lean_ctor_set_tag(v___x_690_, 2);
lean_ctor_set(v___x_690_, 0, v_a_694_);
v___x_696_ = v___x_690_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_694_);
v___x_696_ = v_reuseFailAlloc_699_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; 
v___x_697_ = lean_array_push(v_decls_671_, v___x_696_);
v_c_670_ = v_k_683_;
v_decls_671_ = v___x_697_;
goto _start;
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_del_object(v___x_690_);
lean_dec_ref(v_k_683_);
lean_dec_ref(v_decls_671_);
v_a_700_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_693_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_693_);
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
lean_dec_ref(v_type_685_);
lean_dec_ref(v_params_684_);
lean_dec_ref(v_k_683_);
lean_dec_ref(v_decl_682_);
lean_dec_ref(v_decls_671_);
return v___x_687_;
}
}
case 4:
{
lean_object* v_cases_709_; lean_object* v___x_710_; 
v_cases_709_ = lean_ctor_get(v_c_670_, 0);
lean_inc_ref(v_cases_709_);
lean_dec_ref_known(v_c_670_, 1);
v___x_710_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(v_cases_709_, v_decls_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
return v___x_710_;
}
case 7:
{
lean_object* v_fvarId_711_; lean_object* v_i_712_; lean_object* v_y_713_; lean_object* v_k_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_fvarId_711_ = lean_ctor_get(v_c_670_, 0);
lean_inc(v_fvarId_711_);
v_i_712_ = lean_ctor_get(v_c_670_, 1);
lean_inc(v_i_712_);
v_y_713_ = lean_ctor_get(v_c_670_, 2);
lean_inc(v_y_713_);
v_k_714_ = lean_ctor_get(v_c_670_, 3);
lean_inc_ref(v_k_714_);
lean_dec_ref_known(v_c_670_, 4);
v___x_715_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_715_, 0, v_fvarId_711_);
lean_ctor_set(v___x_715_, 1, v_i_712_);
lean_ctor_set(v___x_715_, 2, v_y_713_);
v___x_716_ = lean_array_push(v_decls_671_, v___x_715_);
v_c_670_ = v_k_714_;
v_decls_671_ = v___x_716_;
goto _start;
}
case 8:
{
lean_object* v_fvarId_718_; lean_object* v_i_719_; lean_object* v_y_720_; lean_object* v_k_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_fvarId_718_ = lean_ctor_get(v_c_670_, 0);
lean_inc(v_fvarId_718_);
v_i_719_ = lean_ctor_get(v_c_670_, 1);
lean_inc(v_i_719_);
v_y_720_ = lean_ctor_get(v_c_670_, 2);
lean_inc(v_y_720_);
v_k_721_ = lean_ctor_get(v_c_670_, 3);
lean_inc_ref(v_k_721_);
lean_dec_ref_known(v_c_670_, 4);
v___x_722_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_722_, 0, v_fvarId_718_);
lean_ctor_set(v___x_722_, 1, v_i_719_);
lean_ctor_set(v___x_722_, 2, v_y_720_);
v___x_723_ = lean_array_push(v_decls_671_, v___x_722_);
v_c_670_ = v_k_721_;
v_decls_671_ = v___x_723_;
goto _start;
}
case 9:
{
lean_object* v_fvarId_725_; lean_object* v_i_726_; lean_object* v_offset_727_; lean_object* v_y_728_; lean_object* v_ty_729_; lean_object* v_k_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_fvarId_725_ = lean_ctor_get(v_c_670_, 0);
lean_inc(v_fvarId_725_);
v_i_726_ = lean_ctor_get(v_c_670_, 1);
lean_inc(v_i_726_);
v_offset_727_ = lean_ctor_get(v_c_670_, 2);
lean_inc(v_offset_727_);
v_y_728_ = lean_ctor_get(v_c_670_, 3);
lean_inc(v_y_728_);
v_ty_729_ = lean_ctor_get(v_c_670_, 4);
lean_inc_ref(v_ty_729_);
v_k_730_ = lean_ctor_get(v_c_670_, 5);
lean_inc_ref(v_k_730_);
lean_dec_ref_known(v_c_670_, 6);
v___x_731_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v___x_731_, 0, v_fvarId_725_);
lean_ctor_set(v___x_731_, 1, v_i_726_);
lean_ctor_set(v___x_731_, 2, v_offset_727_);
lean_ctor_set(v___x_731_, 3, v_y_728_);
lean_ctor_set(v___x_731_, 4, v_ty_729_);
v___x_732_ = lean_array_push(v_decls_671_, v___x_731_);
v_c_670_ = v_k_730_;
v_decls_671_ = v___x_732_;
goto _start;
}
case 10:
{
lean_object* v_fvarId_734_; lean_object* v_cidx_735_; lean_object* v_k_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_fvarId_734_ = lean_ctor_get(v_c_670_, 0);
lean_inc(v_fvarId_734_);
v_cidx_735_ = lean_ctor_get(v_c_670_, 1);
lean_inc(v_cidx_735_);
v_k_736_ = lean_ctor_get(v_c_670_, 2);
lean_inc_ref(v_k_736_);
lean_dec_ref_known(v_c_670_, 3);
v___x_737_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_737_, 0, v_fvarId_734_);
lean_ctor_set(v___x_737_, 1, v_cidx_735_);
v___x_738_ = lean_array_push(v_decls_671_, v___x_737_);
v_c_670_ = v_k_736_;
v_decls_671_ = v___x_738_;
goto _start;
}
case 11:
{
lean_object* v_fvarId_740_; lean_object* v_n_741_; uint8_t v_check_742_; uint8_t v_persistent_743_; lean_object* v_k_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_fvarId_740_ = lean_ctor_get(v_c_670_, 0);
lean_inc(v_fvarId_740_);
v_n_741_ = lean_ctor_get(v_c_670_, 1);
lean_inc(v_n_741_);
v_check_742_ = lean_ctor_get_uint8(v_c_670_, sizeof(void*)*3);
v_persistent_743_ = lean_ctor_get_uint8(v_c_670_, sizeof(void*)*3 + 1);
v_k_744_ = lean_ctor_get(v_c_670_, 2);
lean_inc_ref(v_k_744_);
lean_dec_ref_known(v_c_670_, 3);
v___x_745_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v___x_745_, 0, v_fvarId_740_);
lean_ctor_set(v___x_745_, 1, v_n_741_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*2, v_check_742_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*2 + 1, v_persistent_743_);
v___x_746_ = lean_array_push(v_decls_671_, v___x_745_);
v_c_670_ = v_k_744_;
v_decls_671_ = v___x_746_;
goto _start;
}
case 12:
{
lean_object* v_fvarId_748_; lean_object* v_n_749_; uint8_t v_check_750_; uint8_t v_persistent_751_; lean_object* v_objs_x3f_752_; lean_object* v_k_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_fvarId_748_ = lean_ctor_get(v_c_670_, 0);
lean_inc(v_fvarId_748_);
v_n_749_ = lean_ctor_get(v_c_670_, 1);
lean_inc(v_n_749_);
v_check_750_ = lean_ctor_get_uint8(v_c_670_, sizeof(void*)*4);
v_persistent_751_ = lean_ctor_get_uint8(v_c_670_, sizeof(void*)*4 + 1);
v_objs_x3f_752_ = lean_ctor_get(v_c_670_, 2);
lean_inc(v_objs_x3f_752_);
v_k_753_ = lean_ctor_get(v_c_670_, 3);
lean_inc_ref(v_k_753_);
lean_dec_ref_known(v_c_670_, 4);
v___x_754_ = lean_alloc_ctor(8, 3, 2);
lean_ctor_set(v___x_754_, 0, v_fvarId_748_);
lean_ctor_set(v___x_754_, 1, v_n_749_);
lean_ctor_set(v___x_754_, 2, v_objs_x3f_752_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*3, v_check_750_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*3 + 1, v_persistent_751_);
v___x_755_ = lean_array_push(v_decls_671_, v___x_754_);
v_c_670_ = v_k_753_;
v_decls_671_ = v___x_755_;
goto _start;
}
case 13:
{
lean_object* v_fvarId_757_; lean_object* v_k_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_fvarId_757_ = lean_ctor_get(v_c_670_, 0);
lean_inc(v_fvarId_757_);
v_k_758_ = lean_ctor_get(v_c_670_, 1);
lean_inc_ref(v_k_758_);
lean_dec_ref_known(v_c_670_, 2);
v___x_759_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_759_, 0, v_fvarId_757_);
v___x_760_ = lean_array_push(v_decls_671_, v___x_759_);
v_c_670_ = v_k_758_;
v_decls_671_ = v___x_760_;
goto _start;
}
default: 
{
uint8_t v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = 1;
v___x_763_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_762_, v_decls_671_, v_c_670_);
lean_dec_ref(v_decls_671_);
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(lean_object* v_code_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0));
v___x_772_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(v_code_765_, v___x_771_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___boxed(lean_object* v_i_773_, lean_object* v_as_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2(v_i_773_, v_as_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go___boxed(lean_object* v_c_781_, lean_object* v_decls_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(v_c_781_, v_decls_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___boxed(lean_object* v_c_789_, lean_object* v_decls_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(v_c_789_, v_decls_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(lean_object* v_00_u03b2_797_, lean_object* v_m_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___redArg(v_m_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___boxed(lean_object* v_00_u03b2_800_, lean_object* v_m_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(v_00_u03b2_800_, v_m_801_);
lean_dec_ref(v_m_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4(lean_object* v_00_u03b2_803_, lean_object* v_init_804_, lean_object* v_b_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4___redArg(v_init_804_, v_b_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4___boxed(lean_object* v_00_u03b2_807_, lean_object* v_init_808_, lean_object* v_b_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4(v_00_u03b2_807_, v_init_808_, v_b_809_);
lean_dec_ref(v_b_809_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_811_, lean_object* v_b_812_, lean_object* v_acc_813_, lean_object* v_i_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4_spec__5___redArg(v_b_812_, v_acc_813_, v_i_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_816_, lean_object* v_b_817_, lean_object* v_acc_818_, lean_object* v_i_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3_spec__4_spec__5(v_00_u03b2_816_, v_b_817_, v_acc_818_, v_i_819_);
lean_dec_ref(v_b_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(lean_object* v_f_821_, lean_object* v_v_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
if (lean_obj_tag(v_v_822_) == 0)
{
lean_object* v_code_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_852_; 
v_code_828_ = lean_ctor_get(v_v_822_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v_v_822_);
if (v_isSharedCheck_852_ == 0)
{
v___x_830_ = v_v_822_;
v_isShared_831_ = v_isSharedCheck_852_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_code_828_);
lean_dec(v_v_822_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_852_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; 
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
v___x_832_ = lean_apply_6(v_f_821_, v_code_828_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, lean_box(0));
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_843_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_843_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_843_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_843_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v_a_833_);
v___x_838_ = v___x_830_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_840_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_838_);
v___x_840_ = v___x_835_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_del_object(v___x_830_);
v_a_844_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_832_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_832_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
else
{
lean_object* v___x_853_; 
lean_dec_ref(v_f_821_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v_v_822_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg___boxed(lean_object* v_f_854_, lean_object* v_v_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v_f_854_, v_v_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0(uint8_t v_pu_862_, lean_object* v_f_863_, lean_object* v_v_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v_f_863_, v_v_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___boxed(lean_object* v_pu_871_, lean_object* v_f_872_, lean_object* v_v_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v_pu_boxed_879_; lean_object* v_res_880_; 
v_pu_boxed_879_ = lean_unbox(v_pu_871_);
v_res_880_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0(v_pu_boxed_879_, v_f_872_, v_v_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
return v_res_880_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1(void){
_start:
{
lean_object* v_cellCount_882_; lean_object* v___x_883_; 
v_cellCount_882_ = lean_unsigned_to_nat(16u);
v___x_883_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_882_);
return v___x_883_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2(void){
_start:
{
lean_object* v_cellCount_884_; lean_object* v___x_885_; 
v_cellCount_884_ = lean_unsigned_to_nat(16u);
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_884_);
return v___x_885_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__3(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_886_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2);
v___x_887_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1);
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_887_);
lean_ctor_set(v___x_889_, 2, v___x_886_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj(lean_object* v_decl_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_toSignature_896_; lean_object* v_value_897_; uint8_t v_recursive_898_; lean_object* v_inlineAttr_x3f_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_921_; 
v_toSignature_896_ = lean_ctor_get(v_decl_890_, 0);
v_value_897_ = lean_ctor_get(v_decl_890_, 1);
v_recursive_898_ = lean_ctor_get_uint8(v_decl_890_, sizeof(void*)*3);
v_inlineAttr_x3f_899_ = lean_ctor_get(v_decl_890_, 2);
v_isSharedCheck_921_ = !lean_is_exclusive(v_decl_890_);
if (v_isSharedCheck_921_ == 0)
{
v___x_901_ = v_decl_890_;
v_isShared_902_ = v_isSharedCheck_921_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_inlineAttr_x3f_899_);
lean_inc(v_value_897_);
lean_inc(v_toSignature_896_);
lean_dec(v_decl_890_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_921_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___f_903_; lean_object* v___x_904_; 
v___f_903_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0));
v___x_904_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v___f_903_, v_value_897_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; uint8_t v___x_906_; lean_object* v___x_908_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v___x_906_ = 1;
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v_a_905_);
v___x_908_ = v___x_901_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_toSignature_896_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_a_905_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_inlineAttr_x3f_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3, v_recursive_898_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__3, &l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__3_once, _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__3);
v___x_910_ = 0;
v___x_911_ = l_Lean_Compiler_LCNF_Decl_internalize(v___x_906_, v___x_908_, v___x_909_, v___x_910_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
return v___x_911_;
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_del_object(v___x_901_);
lean_dec(v_inlineAttr_x3f_899_);
lean_dec_ref(v_toSignature_896_);
v_a_913_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_904_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_904_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___boxed(lean_object* v_decl_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj(v_decl_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_pushProj(lean_object* v_occurrence_933_){
_start:
{
lean_object* v___x_934_; uint8_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_934_ = ((lean_object*)(l_Lean_Compiler_LCNF_pushProj___closed__1));
v___x_935_ = 2;
v___x_936_ = ((lean_object*)(l_Lean_Compiler_LCNF_pushProj___closed__2));
v___x_937_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_934_, v___x_935_, v___x_936_, v_occurrence_933_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1008_; uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_));
v___x_1009_ = 1;
v___x_1010_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_));
v___x_1011_ = l_Lean_registerTraceClass(v___x_1008_, v___x_1009_, v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2____boxed(lean_object* v_a_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_();
return v_res_1013_;
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
