// Lean compiler output
// Module: Lean.Compiler.LCNF.CoalesceRC
// Imports: public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.PassManager
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Data.DHashMap.Internal.Defs"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 37, .m_data = "Std.DHashMap.Internal.Raw₀.Const.get!"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_coalesceRC___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "coalesceRc"};
static const lean_object* l_Lean_Compiler_LCNF_coalesceRC___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_coalesceRC___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_coalesceRC___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_coalesceRC___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 114, 246, 206, 217, 190, 252, 129)}};
static const lean_object* l_Lean_Compiler_LCNF_coalesceRC___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_coalesceRC___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_coalesceRC___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_coalesceRC___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_coalesceRC___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_coalesceRC___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_coalesceRC___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_coalesceRC;
static const lean_string_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_coalesceRC___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 216, 54, 222, 197, 106, 200, 120)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "CoalesceRC"};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 64, 198, 19, 206, 33, 62, 79)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(107, 8, 174, 237, 20, 86, 219, 140)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 31, 21, 218, 80, 138, 95, 71)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 231, 9, 30, 247, 225, 35, 65)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 100, 167, 44, 28, 227, 152, 210)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 147, 252, 63, 173, 48, 139, 202)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 48, 141, 29, 244, 35, 164, 12)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 159, 167, 89, 224, 31, 118, 195)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(154, 248, 169, 172, 55, 216, 59, 199)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 108, 213, 163, 132, 191, 152, 236)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(184, 118, 24, 174, 71, 162, 45, 148)}};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4(lean_object* v_msg_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = lean_panic_fn_borrowed(v___x_2_, v_msg_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__6___redArg(lean_object* v_m_4_, lean_object* v_query_5_, lean_object* v_x_6_, lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
lean_object* v_zero_9_; uint8_t v_isZero_10_; 
v_zero_9_ = lean_unsigned_to_nat(0u);
v_isZero_10_ = lean_nat_dec_eq(v_x_7_, v_zero_9_);
if (v_isZero_10_ == 1)
{
lean_dec(v_x_8_);
lean_dec(v_x_7_);
if (lean_obj_tag(v_x_6_) == 0)
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(2);
return v___x_11_;
}
else
{
lean_object* v_val_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_19_; 
v_val_12_ = lean_ctor_get(v_x_6_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v_x_6_);
if (v_isSharedCheck_19_ == 0)
{
v___x_14_ = v_x_6_;
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_val_12_);
lean_dec(v_x_6_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_15_ == 0)
{
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_val_12_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
else
{
lean_object* v_keyArray_20_; lean_object* v_valueArray_21_; lean_object* v___x_22_; uint8_t v_isSome_23_; 
v_keyArray_20_ = lean_ctor_get(v_m_4_, 1);
v_valueArray_21_ = lean_ctor_get(v_m_4_, 2);
v___x_22_ = lean_array_fget_borrowed(v_keyArray_20_, v_x_8_);
v_isSome_23_ = lean_noption_is_some(v___x_22_);
if (v_isSome_23_ == 0)
{
lean_dec(v_x_7_);
if (lean_obj_tag(v_x_6_) == 0)
{
lean_object* v___x_24_; 
v___x_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_24_, 0, v_x_8_);
return v___x_24_;
}
else
{
lean_object* v_val_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_dec(v_x_8_);
v_val_25_ = lean_ctor_get(v_x_6_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v_x_6_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v_x_6_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_val_25_);
lean_dec(v_x_6_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_val_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
else
{
lean_object* v_one_33_; lean_object* v_n_34_; lean_object* v___y_36_; 
v_one_33_ = lean_unsigned_to_nat(1u);
v_n_34_ = lean_nat_sub(v_x_7_, v_one_33_);
lean_dec(v_x_7_);
if (v_isSome_23_ == 0)
{
goto v___jp_42_;
}
else
{
lean_object* v___x_44_; uint8_t v_isSome_45_; 
v___x_44_ = lean_array_fget_borrowed(v_valueArray_21_, v_x_8_);
v_isSome_45_ = lean_noption_is_some(v___x_44_);
if (v_isSome_45_ == 0)
{
goto v___jp_42_;
}
else
{
lean_object* v_val_46_; uint8_t v___x_47_; 
lean_inc(v___x_22_);
v_val_46_ = lean_noption_get(v___x_22_);
v___x_47_ = l_Lean_instBEqFVarId_beq(v_val_46_, v_query_5_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
lean_dec(v_val_46_);
v___x_48_ = lean_array_get_size(v_keyArray_20_);
v___x_49_ = lean_nat_add(v_x_8_, v_one_33_);
lean_dec(v_x_8_);
v___x_50_ = lean_nat_dec_lt(v___x_49_, v___x_48_);
if (v___x_50_ == 0)
{
lean_dec(v___x_49_);
v_x_7_ = v_n_34_;
v_x_8_ = v_zero_9_;
goto _start;
}
else
{
v_x_7_ = v_n_34_;
v_x_8_ = v___x_49_;
goto _start;
}
}
else
{
lean_object* v_val_53_; lean_object* v___x_54_; 
lean_dec(v_n_34_);
lean_dec(v_x_6_);
lean_inc(v___x_44_);
v_val_53_ = lean_noption_get(v___x_44_);
v___x_54_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_54_, 0, v_x_8_);
lean_ctor_set(v___x_54_, 1, v_val_46_);
lean_ctor_set(v___x_54_, 2, v_val_53_);
return v___x_54_;
}
}
}
v___jp_35_:
{
lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_37_ = lean_array_get_size(v_keyArray_20_);
v___x_38_ = lean_nat_add(v_x_8_, v_one_33_);
lean_dec(v_x_8_);
v___x_39_ = lean_nat_dec_lt(v___x_38_, v___x_37_);
if (v___x_39_ == 0)
{
lean_dec(v___x_38_);
v_x_6_ = v___y_36_;
v_x_7_ = v_n_34_;
v_x_8_ = v_zero_9_;
goto _start;
}
else
{
v_x_6_ = v___y_36_;
v_x_7_ = v_n_34_;
v_x_8_ = v___x_38_;
goto _start;
}
}
v___jp_42_:
{
if (lean_obj_tag(v_x_6_) == 0)
{
lean_object* v___x_43_; 
lean_inc(v_x_8_);
v___x_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_43_, 0, v_x_8_);
v___y_36_ = v___x_43_;
goto v___jp_35_;
}
else
{
v___y_36_ = v_x_6_;
goto v___jp_35_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__6___redArg___boxed(lean_object* v_m_55_, lean_object* v_query_56_, lean_object* v_x_57_, lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__6___redArg(v_m_55_, v_query_56_, v_x_57_, v_x_58_, v_x_59_);
lean_dec(v_query_56_);
lean_dec_ref(v_m_55_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(lean_object* v_m_61_, lean_object* v_query_62_){
_start:
{
lean_object* v_keyArray_63_; lean_object* v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v_fold_68_; uint64_t v___x_69_; uint64_t v___x_70_; uint64_t v___x_71_; size_t v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_keyArray_63_ = lean_ctor_get(v_m_61_, 1);
v___x_64_ = lean_array_get_size(v_keyArray_63_);
v___x_65_ = l_Lean_instHashableFVarId_hash(v_query_62_);
v___x_66_ = 32ULL;
v___x_67_ = lean_uint64_shift_right(v___x_65_, v___x_66_);
v_fold_68_ = lean_uint64_xor(v___x_65_, v___x_67_);
v___x_69_ = 16ULL;
v___x_70_ = lean_uint64_shift_right(v_fold_68_, v___x_69_);
v___x_71_ = lean_uint64_xor(v_fold_68_, v___x_70_);
v___x_72_ = lean_uint64_to_usize(v___x_71_);
v___x_73_ = lean_usize_of_nat(v___x_64_);
v___x_74_ = ((size_t)1ULL);
v___x_75_ = lean_usize_sub(v___x_73_, v___x_74_);
v___x_76_ = lean_usize_land(v___x_72_, v___x_75_);
v___x_77_ = lean_usize_to_nat(v___x_76_);
v___x_78_ = lean_box(0);
v___x_79_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__6___redArg(v_m_61_, v_query_62_, v___x_78_, v___x_64_, v___x_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg___boxed(lean_object* v_m_80_, lean_object* v_query_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v_m_80_, v_query_81_);
lean_dec(v_query_81_);
lean_dec_ref(v_m_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5_spec__10___redArg(lean_object* v_m_83_, lean_object* v_query_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v_m_83_, v_query_84_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_index_86_; lean_object* v_key_87_; lean_object* v_value_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_index_86_ = lean_ctor_get(v___x_85_, 0);
v_key_87_ = lean_ctor_get(v___x_85_, 1);
v_value_88_ = lean_ctor_get(v___x_85_, 2);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_85_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_value_88_);
lean_inc(v_key_87_);
lean_inc(v_index_86_);
lean_dec(v___x_85_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_index_86_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_key_87_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v_value_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v___x_85_);
v___x_96_ = lean_box(1);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5_spec__10___redArg___boxed(lean_object* v_m_97_, lean_object* v_query_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5_spec__10___redArg(v_m_97_, v_query_98_);
lean_dec(v_query_98_);
lean_dec_ref(v_m_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg(lean_object* v_m_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5_spec__10___redArg(v_m_100_, v_a_101_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_value_103_; lean_object* v___x_104_; 
v_value_103_ = lean_ctor_get(v___x_102_, 2);
lean_inc(v_value_103_);
lean_dec_ref_known(v___x_102_, 3);
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v_value_103_);
return v___x_104_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_box(0);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg___boxed(lean_object* v_m_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg(v_m_106_, v_a_107_);
lean_dec(v_a_107_);
lean_dec_ref(v_m_106_);
return v_res_108_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_112_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__2));
v___x_113_ = lean_unsigned_to_nat(12u);
v___x_114_ = lean_unsigned_to_nat(672u);
v___x_115_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__1));
v___x_116_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__0));
v___x_117_ = l_mkPanicMessageWithDecl(v___x_116_, v___x_115_, v___x_114_, v___x_113_, v___x_112_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2(lean_object* v_m_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg(v_m_118_, v_a_119_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___closed__3);
v___x_122_ = l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4(v___x_121_);
return v___x_122_;
}
else
{
lean_object* v_val_123_; 
v_val_123_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v___x_120_, 1);
return v_val_123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2___boxed(lean_object* v_m_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2(v_m_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_m_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8_spec__9___redArg(lean_object* v_b_127_, lean_object* v_acc_128_, lean_object* v_i_129_){
_start:
{
lean_object* v___y_131_; lean_object* v_keyArray_139_; lean_object* v_valueArray_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_keyArray_139_ = lean_ctor_get(v_b_127_, 1);
v_valueArray_140_ = lean_ctor_get(v_b_127_, 2);
v___x_141_ = lean_array_get_size(v_keyArray_139_);
v___x_142_ = lean_nat_dec_lt(v_i_129_, v___x_141_);
if (v___x_142_ == 0)
{
lean_dec(v_i_129_);
return v_acc_128_;
}
else
{
lean_object* v___x_143_; uint8_t v_isSome_144_; 
v___x_143_ = lean_array_fget_borrowed(v_keyArray_139_, v_i_129_);
v_isSome_144_ = lean_noption_is_some(v___x_143_);
if (v_isSome_144_ == 0)
{
goto v___jp_135_;
}
else
{
lean_object* v___x_145_; uint8_t v_isSome_146_; 
v___x_145_ = lean_array_fget_borrowed(v_valueArray_140_, v_i_129_);
v_isSome_146_ = lean_noption_is_some(v___x_145_);
if (v_isSome_146_ == 0)
{
goto v___jp_135_;
}
else
{
lean_object* v_val_147_; lean_object* v_val_148_; lean_object* v_i_150_; lean_object* v___x_155_; 
lean_inc(v___x_143_);
v_val_147_ = lean_noption_get(v___x_143_);
lean_inc(v___x_145_);
v_val_148_ = lean_noption_get(v___x_145_);
v___x_155_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v_acc_128_, v_val_147_);
switch(lean_obj_tag(v___x_155_))
{
case 0:
{
lean_object* v_index_156_; lean_object* v_size_157_; lean_object* v___x_158_; 
v_index_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_index_156_);
lean_dec_ref_known(v___x_155_, 3);
v_size_157_ = lean_ctor_get(v_acc_128_, 0);
lean_inc(v_size_157_);
v___x_158_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_128_, v_size_157_, v_index_156_, v_val_147_, v_val_148_);
lean_dec(v_index_156_);
v___y_131_ = v___x_158_;
goto v___jp_130_;
}
case 1:
{
lean_object* v_index_159_; 
v_index_159_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_index_159_);
lean_dec_ref_known(v___x_155_, 1);
v_i_150_ = v_index_159_;
goto v___jp_149_;
}
default: 
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_128_, v___x_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_index_162_; 
v_index_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_index_162_);
lean_dec_ref_known(v___x_161_, 1);
v_i_150_ = v_index_162_;
goto v___jp_149_;
}
else
{
lean_dec(v_val_148_);
lean_dec(v_val_147_);
v___y_131_ = v_acc_128_;
goto v___jp_130_;
}
}
}
v___jp_149_:
{
lean_object* v_size_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_size_151_ = lean_ctor_get(v_acc_128_, 0);
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = lean_nat_add(v_size_151_, v___x_152_);
v___x_154_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_128_, v___x_153_, v_i_150_, v_val_147_, v_val_148_);
lean_dec(v_i_150_);
v___y_131_ = v___x_154_;
goto v___jp_130_;
}
}
}
}
v___jp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_add(v_i_129_, v___x_132_);
lean_dec(v_i_129_);
v_acc_128_ = v___y_131_;
v_i_129_ = v___x_133_;
goto _start;
}
v___jp_135_:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_i_129_, v___x_136_);
lean_dec(v_i_129_);
v_i_129_ = v___x_137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8_spec__9___redArg___boxed(lean_object* v_b_163_, lean_object* v_acc_164_, lean_object* v_i_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8_spec__9___redArg(v_b_163_, v_acc_164_, v_i_165_);
lean_dec_ref(v_b_163_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8___redArg(lean_object* v_init_167_, lean_object* v_b_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8_spec__9___redArg(v_b_168_, v_init_167_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8___redArg___boxed(lean_object* v_init_171_, lean_object* v_b_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8___redArg(v_init_171_, v_b_172_);
lean_dec_ref(v_b_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(lean_object* v_m_174_){
_start:
{
lean_object* v_keyArray_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v_cellCount_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_target_182_; lean_object* v___x_183_; 
v_keyArray_175_ = lean_ctor_get(v_m_174_, 1);
v___x_176_ = lean_array_get_size(v_keyArray_175_);
v___x_177_ = lean_unsigned_to_nat(2u);
v_cellCount_178_ = lean_nat_mul(v___x_176_, v___x_177_);
v___x_179_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_178_);
v___x_180_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_178_);
v___x_181_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_178_);
v_target_182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_182_, 0, v___x_179_);
lean_ctor_set(v_target_182_, 1, v___x_180_);
lean_ctor_set(v_target_182_, 2, v___x_181_);
v___x_183_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8___redArg(v_target_182_, v_m_174_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg___boxed(lean_object* v_m_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_m_184_);
lean_dec_ref(v_m_184_);
return v_res_185_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5___redArg(lean_object* v_m_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5_spec__10___redArg(v_m_186_, v_a_187_);
if (lean_obj_tag(v___x_188_) == 0)
{
uint8_t v___x_189_; 
lean_dec_ref_known(v___x_188_, 3);
v___x_189_ = 1;
return v___x_189_;
}
else
{
uint8_t v___x_190_; 
v___x_190_ = 0;
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5___redArg___boxed(lean_object* v_m_191_, lean_object* v_a_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5___redArg(v_m_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_m_191_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0(lean_object* v_n_195_, lean_object* v_v_x3f_196_){
_start:
{
lean_object* v___y_198_; 
if (lean_obj_tag(v_v_x3f_196_) == 0)
{
lean_object* v___x_201_; 
v___x_201_ = lean_unsigned_to_nat(0u);
v___y_198_ = v___x_201_;
goto v___jp_197_;
}
else
{
lean_object* v_val_202_; 
v_val_202_ = lean_ctor_get(v_v_x3f_196_, 0);
v___y_198_ = v_val_202_;
goto v___jp_197_;
}
v___jp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_nat_add(v___y_198_, v_n_195_);
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0___boxed(lean_object* v_n_203_, lean_object* v_v_x3f_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0(v_n_203_, v_v_x3f_204_);
lean_dec(v_v_x3f_204_);
lean_dec(v_n_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___redArg(lean_object* v_alt_206_, lean_object* v_f_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___y_215_; 
switch(lean_obj_tag(v_alt_206_))
{
case 0:
{
lean_object* v_code_234_; 
v_code_234_ = lean_ctor_get(v_alt_206_, 2);
lean_inc_ref(v_code_234_);
v___y_215_ = v_code_234_;
goto v___jp_214_;
}
case 1:
{
lean_object* v_code_235_; 
v_code_235_ = lean_ctor_get(v_alt_206_, 1);
lean_inc_ref(v_code_235_);
v___y_215_ = v_code_235_;
goto v___jp_214_;
}
default: 
{
lean_object* v_code_236_; 
v_code_236_ = lean_ctor_get(v_alt_206_, 0);
lean_inc_ref(v_code_236_);
v___y_215_ = v_code_236_;
goto v___jp_214_;
}
}
v___jp_214_:
{
lean_object* v___x_216_; 
lean_inc(v___y_212_);
lean_inc_ref(v___y_211_);
lean_inc(v___y_210_);
lean_inc_ref(v___y_209_);
lean_inc(v___y_208_);
v___x_216_ = lean_apply_7(v_f_207_, v___y_215_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, lean_box(0));
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_225_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_225_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_221_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_206_, v_a_217_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_221_);
v___x_223_ = v___x_219_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
lean_dec_ref(v_alt_206_);
v_a_226_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_216_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_216_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___redArg___boxed(lean_object* v_alt_237_, lean_object* v_f_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___redArg(v_alt_237_, v_f_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
return v_res_245_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__1(void){
_start:
{
lean_object* v_cellCount_246_; lean_object* v___x_247_; 
v_cellCount_246_ = lean_unsigned_to_nat(16u);
v___x_247_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_246_);
return v___x_247_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__0(void){
_start:
{
lean_object* v_cellCount_248_; lean_object* v___x_249_; 
v_cellCount_248_ = lean_unsigned_to_nat(16u);
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_248_);
return v___x_249_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__2(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_250_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__1, &l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__1_once, _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__1);
v___x_251_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__0, &l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__0_once, _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__0);
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
lean_ctor_set(v___x_253_, 2, v___x_250_);
return v___x_253_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__3(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__2, &l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__2_once, _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__2);
v___x_255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
lean_ctor_set(v___x_255_, 2, v___x_254_);
lean_ctor_set(v___x_255_, 3, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1___lam__0___boxed(lean_object* v_x_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1___lam__0(v_x_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1(lean_object* v_i_264_, lean_object* v_as_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_array_get_size(v_as_265_);
v___x_273_ = lean_nat_dec_lt(v_i_264_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
lean_dec(v_i_264_);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v_as_265_);
return v___x_274_;
}
else
{
lean_object* v___f_275_; lean_object* v_a_276_; lean_object* v___x_277_; 
v___f_275_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1___lam__0___boxed), 7, 0);
v_a_276_ = lean_array_fget_borrowed(v_as_265_, v_i_264_);
lean_inc(v_a_276_);
v___x_277_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___redArg(v_a_276_, v___f_275_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; size_t v___x_279_; size_t v___x_280_; uint8_t v___x_281_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_a_278_);
lean_dec_ref_known(v___x_277_, 1);
v___x_279_ = lean_ptr_addr(v_a_276_);
v___x_280_ = lean_ptr_addr(v_a_278_);
v___x_281_ = lean_usize_dec_eq(v___x_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_add(v_i_264_, v___x_282_);
v___x_284_ = lean_array_fset(v_as_265_, v_i_264_, v_a_278_);
lean_dec(v_i_264_);
v_i_264_ = v___x_283_;
v_as_265_ = v___x_284_;
goto _start;
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v_a_278_);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_i_264_, v___x_286_);
lean_dec(v_i_264_);
v_i_264_ = v___x_287_;
goto _start;
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec_ref(v_as_265_);
lean_dec(v_i_264_);
v_a_289_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_277_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_277_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(lean_object* v_code_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
switch(lean_obj_tag(v_code_297_))
{
case 0:
{
lean_object* v_decl_304_; lean_object* v_k_305_; lean_object* v___x_306_; 
v_decl_304_ = lean_ctor_get(v_code_297_, 0);
v_k_305_ = lean_ctor_get(v_code_297_, 1);
lean_inc_ref(v_k_305_);
v___x_306_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_305_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_329_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_329_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_329_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_329_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
size_t v___x_311_; size_t v___x_312_; uint8_t v___x_313_; 
v___x_311_ = lean_ptr_addr(v_k_305_);
v___x_312_ = lean_ptr_addr(v_a_307_);
v___x_313_ = lean_usize_dec_eq(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_323_; 
lean_inc_ref(v_decl_304_);
v_isSharedCheck_323_ = !lean_is_exclusive(v_code_297_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; lean_object* v_unused_325_; 
v_unused_324_ = lean_ctor_get(v_code_297_, 1);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_code_297_, 0);
lean_dec(v_unused_325_);
v___x_315_ = v_code_297_;
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
else
{
lean_dec(v_code_297_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v_a_307_);
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_decl_304_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_a_307_);
v___x_318_ = v_reuseFailAlloc_322_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_320_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_318_);
v___x_320_ = v___x_309_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
else
{
lean_object* v___x_327_; 
lean_dec(v_a_307_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v_code_297_);
v___x_327_ = v___x_309_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_code_297_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_297_, 2);
return v___x_306_;
}
}
case 2:
{
lean_object* v_decl_330_; lean_object* v_k_331_; lean_object* v_params_332_; lean_object* v_type_333_; lean_object* v_value_334_; lean_object* v___x_335_; 
v_decl_330_ = lean_ctor_get(v_code_297_, 0);
v_k_331_ = lean_ctor_get(v_code_297_, 1);
v_params_332_ = lean_ctor_get(v_decl_330_, 2);
v_type_333_ = lean_ctor_get(v_decl_330_, 3);
v_value_334_ = lean_ctor_get(v_decl_330_, 4);
lean_inc_ref(v_value_334_);
v___x_335_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC(v_value_334_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; uint8_t v___x_337_; lean_object* v___x_338_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_335_, 1);
v___x_337_ = 1;
lean_inc_ref(v_params_332_);
lean_inc_ref(v_type_333_);
lean_inc_ref(v_decl_330_);
v___x_338_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_337_, v_decl_330_, v_type_333_, v_params_332_, v_a_336_, v_a_300_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_340_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref_known(v___x_338_, 1);
lean_inc_ref(v_k_331_);
v___x_340_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_331_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_368_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_368_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_368_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_368_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
uint8_t v___y_346_; size_t v___x_362_; size_t v___x_363_; uint8_t v___x_364_; 
v___x_362_ = lean_ptr_addr(v_k_331_);
v___x_363_ = lean_ptr_addr(v_a_341_);
v___x_364_ = lean_usize_dec_eq(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
v___y_346_ = v___x_364_;
goto v___jp_345_;
}
else
{
size_t v___x_365_; size_t v___x_366_; uint8_t v___x_367_; 
v___x_365_ = lean_ptr_addr(v_decl_330_);
v___x_366_ = lean_ptr_addr(v_a_339_);
v___x_367_ = lean_usize_dec_eq(v___x_365_, v___x_366_);
v___y_346_ = v___x_367_;
goto v___jp_345_;
}
v___jp_345_:
{
if (v___y_346_ == 0)
{
lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_356_; 
v_isSharedCheck_356_ = !lean_is_exclusive(v_code_297_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; lean_object* v_unused_358_; 
v_unused_357_ = lean_ctor_get(v_code_297_, 1);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v_code_297_, 0);
lean_dec(v_unused_358_);
v___x_348_ = v_code_297_;
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
else
{
lean_dec(v_code_297_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v_a_341_);
lean_ctor_set(v___x_348_, 0, v_a_339_);
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_339_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_a_341_);
v___x_351_ = v_reuseFailAlloc_355_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_353_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_351_);
v___x_353_ = v___x_343_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
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
else
{
lean_object* v___x_360_; 
lean_dec(v_a_341_);
lean_dec(v_a_339_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v_code_297_);
v___x_360_ = v___x_343_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_code_297_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
else
{
lean_dec(v_a_339_);
lean_dec_ref_known(v_code_297_, 2);
return v___x_340_;
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec_ref_known(v_code_297_, 2);
v_a_369_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_338_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_338_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_297_, 2);
return v___x_335_;
}
}
case 4:
{
lean_object* v_cases_377_; lean_object* v_typeName_378_; lean_object* v_resultType_379_; lean_object* v_discr_380_; lean_object* v_alts_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_420_; 
v_cases_377_ = lean_ctor_get(v_code_297_, 0);
lean_inc_ref(v_cases_377_);
v_typeName_378_ = lean_ctor_get(v_cases_377_, 0);
v_resultType_379_ = lean_ctor_get(v_cases_377_, 1);
v_discr_380_ = lean_ctor_get(v_cases_377_, 2);
v_alts_381_ = lean_ctor_get(v_cases_377_, 3);
v_isSharedCheck_420_ = !lean_is_exclusive(v_cases_377_);
if (v_isSharedCheck_420_ == 0)
{
v___x_383_ = v_cases_377_;
v_isShared_384_ = v_isSharedCheck_420_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_alts_381_);
lean_inc(v_discr_380_);
lean_inc(v_resultType_379_);
lean_inc(v_typeName_378_);
lean_dec(v_cases_377_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_420_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_381_);
v___x_386_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1(v___x_385_, v_alts_381_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_411_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_411_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_411_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_411_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
size_t v___x_391_; size_t v___x_392_; uint8_t v___x_393_; 
v___x_391_ = lean_ptr_addr(v_alts_381_);
lean_dec_ref(v_alts_381_);
v___x_392_ = lean_ptr_addr(v_a_387_);
v___x_393_ = lean_usize_dec_eq(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_406_; 
v_isSharedCheck_406_ = !lean_is_exclusive(v_code_297_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v_code_297_, 0);
lean_dec(v_unused_407_);
v___x_395_ = v_code_297_;
v_isShared_396_ = v_isSharedCheck_406_;
goto v_resetjp_394_;
}
else
{
lean_dec(v_code_297_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_406_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 3, v_a_387_);
v___x_398_ = v___x_383_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_typeName_378_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_resultType_379_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_discr_380_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_a_387_);
v___x_398_ = v_reuseFailAlloc_405_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_400_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_398_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_404_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_402_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_400_);
v___x_402_ = v___x_389_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
else
{
lean_object* v___x_409_; 
lean_dec(v_a_387_);
lean_del_object(v___x_383_);
lean_dec(v_discr_380_);
lean_dec_ref(v_resultType_379_);
lean_dec(v_typeName_378_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v_code_297_);
v___x_409_ = v___x_389_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_code_297_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_del_object(v___x_383_);
lean_dec_ref(v_alts_381_);
lean_dec(v_discr_380_);
lean_dec_ref(v_resultType_379_);
lean_dec(v_typeName_378_);
lean_dec_ref_known(v_code_297_, 1);
v_a_412_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_386_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_386_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_421_; lean_object* v_i_422_; lean_object* v_y_423_; lean_object* v_k_424_; lean_object* v___x_425_; 
v_fvarId_421_ = lean_ctor_get(v_code_297_, 0);
v_i_422_ = lean_ctor_get(v_code_297_, 1);
v_y_423_ = lean_ctor_get(v_code_297_, 2);
v_k_424_ = lean_ctor_get(v_code_297_, 3);
lean_inc_ref(v_k_424_);
v___x_425_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_424_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_450_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_450_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_450_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_450_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
size_t v___x_430_; size_t v___x_431_; uint8_t v___x_432_; 
v___x_430_ = lean_ptr_addr(v_k_424_);
v___x_431_ = lean_ptr_addr(v_a_426_);
v___x_432_ = lean_usize_dec_eq(v___x_430_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_442_; 
lean_inc(v_y_423_);
lean_inc(v_i_422_);
lean_inc(v_fvarId_421_);
v_isSharedCheck_442_ = !lean_is_exclusive(v_code_297_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; lean_object* v_unused_444_; lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_443_ = lean_ctor_get(v_code_297_, 3);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_code_297_, 2);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_code_297_, 1);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_code_297_, 0);
lean_dec(v_unused_446_);
v___x_434_ = v_code_297_;
v_isShared_435_ = v_isSharedCheck_442_;
goto v_resetjp_433_;
}
else
{
lean_dec(v_code_297_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_442_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 3, v_a_426_);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_fvarId_421_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_i_422_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_y_423_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v_a_426_);
v___x_437_ = v_reuseFailAlloc_441_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_437_);
v___x_439_ = v___x_428_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_object* v___x_448_; 
lean_dec(v_a_426_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v_code_297_);
v___x_448_ = v___x_428_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_code_297_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_297_, 4);
return v___x_425_;
}
}
case 8:
{
lean_object* v_fvarId_451_; lean_object* v_i_452_; lean_object* v_y_453_; lean_object* v_k_454_; lean_object* v___x_455_; 
v_fvarId_451_ = lean_ctor_get(v_code_297_, 0);
v_i_452_ = lean_ctor_get(v_code_297_, 1);
v_y_453_ = lean_ctor_get(v_code_297_, 2);
v_k_454_ = lean_ctor_get(v_code_297_, 3);
lean_inc_ref(v_k_454_);
v___x_455_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_454_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_480_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_480_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_480_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_480_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
size_t v___x_460_; size_t v___x_461_; uint8_t v___x_462_; 
v___x_460_ = lean_ptr_addr(v_k_454_);
v___x_461_ = lean_ptr_addr(v_a_456_);
v___x_462_ = lean_usize_dec_eq(v___x_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_472_; 
lean_inc(v_y_453_);
lean_inc(v_i_452_);
lean_inc(v_fvarId_451_);
v_isSharedCheck_472_ = !lean_is_exclusive(v_code_297_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; 
v_unused_473_ = lean_ctor_get(v_code_297_, 3);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_code_297_, 2);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_code_297_, 1);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_code_297_, 0);
lean_dec(v_unused_476_);
v___x_464_ = v_code_297_;
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
else
{
lean_dec(v_code_297_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 3, v_a_456_);
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_fvarId_451_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_i_452_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_y_453_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v_a_456_);
v___x_467_ = v_reuseFailAlloc_471_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_469_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_467_);
v___x_469_ = v___x_458_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v___x_478_; 
lean_dec(v_a_456_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v_code_297_);
v___x_478_ = v___x_458_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_code_297_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_297_, 4);
return v___x_455_;
}
}
case 9:
{
lean_object* v_fvarId_481_; lean_object* v_i_482_; lean_object* v_offset_483_; lean_object* v_y_484_; lean_object* v_ty_485_; lean_object* v_k_486_; lean_object* v___x_487_; 
v_fvarId_481_ = lean_ctor_get(v_code_297_, 0);
v_i_482_ = lean_ctor_get(v_code_297_, 1);
v_offset_483_ = lean_ctor_get(v_code_297_, 2);
v_y_484_ = lean_ctor_get(v_code_297_, 3);
v_ty_485_ = lean_ctor_get(v_code_297_, 4);
v_k_486_ = lean_ctor_get(v_code_297_, 5);
lean_inc_ref(v_k_486_);
v___x_487_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_486_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_514_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_514_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_514_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_514_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
size_t v___x_492_; size_t v___x_493_; uint8_t v___x_494_; 
v___x_492_ = lean_ptr_addr(v_k_486_);
v___x_493_ = lean_ptr_addr(v_a_488_);
v___x_494_ = lean_usize_dec_eq(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_504_; 
lean_inc_ref(v_ty_485_);
lean_inc(v_y_484_);
lean_inc(v_offset_483_);
lean_inc(v_i_482_);
lean_inc(v_fvarId_481_);
v_isSharedCheck_504_ = !lean_is_exclusive(v_code_297_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; lean_object* v_unused_506_; lean_object* v_unused_507_; lean_object* v_unused_508_; lean_object* v_unused_509_; lean_object* v_unused_510_; 
v_unused_505_ = lean_ctor_get(v_code_297_, 5);
lean_dec(v_unused_505_);
v_unused_506_ = lean_ctor_get(v_code_297_, 4);
lean_dec(v_unused_506_);
v_unused_507_ = lean_ctor_get(v_code_297_, 3);
lean_dec(v_unused_507_);
v_unused_508_ = lean_ctor_get(v_code_297_, 2);
lean_dec(v_unused_508_);
v_unused_509_ = lean_ctor_get(v_code_297_, 1);
lean_dec(v_unused_509_);
v_unused_510_ = lean_ctor_get(v_code_297_, 0);
lean_dec(v_unused_510_);
v___x_496_ = v_code_297_;
v_isShared_497_ = v_isSharedCheck_504_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_code_297_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_504_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 5, v_a_488_);
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_fvarId_481_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_i_482_);
lean_ctor_set(v_reuseFailAlloc_503_, 2, v_offset_483_);
lean_ctor_set(v_reuseFailAlloc_503_, 3, v_y_484_);
lean_ctor_set(v_reuseFailAlloc_503_, 4, v_ty_485_);
lean_ctor_set(v_reuseFailAlloc_503_, 5, v_a_488_);
v___x_499_ = v_reuseFailAlloc_503_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_501_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_499_);
v___x_501_ = v___x_490_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v___x_512_; 
lean_dec(v_a_488_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v_code_297_);
v___x_512_ = v___x_490_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_code_297_);
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
lean_dec_ref_known(v_code_297_, 6);
return v___x_487_;
}
}
case 10:
{
lean_object* v_fvarId_515_; lean_object* v_cidx_516_; lean_object* v_k_517_; lean_object* v___x_518_; 
v_fvarId_515_ = lean_ctor_get(v_code_297_, 0);
v_cidx_516_ = lean_ctor_get(v_code_297_, 1);
v_k_517_ = lean_ctor_get(v_code_297_, 2);
lean_inc_ref(v_k_517_);
v___x_518_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_517_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_542_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_542_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_542_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_542_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
size_t v___x_523_; size_t v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_ptr_addr(v_k_517_);
v___x_524_ = lean_ptr_addr(v_a_519_);
v___x_525_ = lean_usize_dec_eq(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_535_; 
lean_inc(v_cidx_516_);
lean_inc(v_fvarId_515_);
v_isSharedCheck_535_ = !lean_is_exclusive(v_code_297_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; lean_object* v_unused_537_; lean_object* v_unused_538_; 
v_unused_536_ = lean_ctor_get(v_code_297_, 2);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v_code_297_, 1);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_code_297_, 0);
lean_dec(v_unused_538_);
v___x_527_ = v_code_297_;
v_isShared_528_ = v_isSharedCheck_535_;
goto v_resetjp_526_;
}
else
{
lean_dec(v_code_297_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_535_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 2, v_a_519_);
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_fvarId_515_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_cidx_516_);
lean_ctor_set(v_reuseFailAlloc_534_, 2, v_a_519_);
v___x_530_ = v_reuseFailAlloc_534_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_530_);
v___x_532_ = v___x_521_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v___x_540_; 
lean_dec(v_a_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v_code_297_);
v___x_540_ = v___x_521_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_code_297_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_297_, 3);
return v___x_518_;
}
}
case 11:
{
lean_object* v_fvarId_543_; lean_object* v_n_544_; uint8_t v_check_545_; uint8_t v_persistent_546_; lean_object* v_k_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_775_; 
v_fvarId_543_ = lean_ctor_get(v_code_297_, 0);
v_n_544_ = lean_ctor_get(v_code_297_, 1);
v_check_545_ = lean_ctor_get_uint8(v_code_297_, sizeof(void*)*3);
v_persistent_546_ = lean_ctor_get_uint8(v_code_297_, sizeof(void*)*3 + 1);
v_k_547_ = lean_ctor_get(v_code_297_, 2);
v_isSharedCheck_775_ = !lean_is_exclusive(v_code_297_);
if (v_isSharedCheck_775_ == 0)
{
v___x_549_ = v_code_297_;
v_isShared_550_ = v_isSharedCheck_775_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_k_547_);
lean_inc(v_n_544_);
lean_inc(v_fvarId_543_);
lean_dec(v_code_297_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_775_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v_i_577_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v_i_605_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___x_625_; lean_object* v_incTotal_626_; lean_object* v_decTotal_627_; lean_object* v_incAccum_628_; lean_object* v_decPlaced_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_774_; 
v___x_625_ = lean_st_ref_take(v_a_298_);
v_incTotal_626_ = lean_ctor_get(v___x_625_, 0);
v_decTotal_627_ = lean_ctor_get(v___x_625_, 1);
v_incAccum_628_ = lean_ctor_get(v___x_625_, 2);
v_decPlaced_629_ = lean_ctor_get(v___x_625_, 3);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_774_ == 0)
{
v___x_631_ = v___x_625_;
v_isShared_632_ = v_isSharedCheck_774_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_decPlaced_629_);
lean_inc(v_incAccum_628_);
lean_inc(v_decTotal_627_);
lean_inc(v_incTotal_626_);
lean_dec(v___x_625_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_774_;
goto v_resetjp_630_;
}
v___jp_551_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v_incTotal_560_; lean_object* v_incAccum_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_557_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_557_, 0, v___y_552_);
lean_ctor_set(v___x_557_, 1, v___y_554_);
lean_ctor_set(v___x_557_, 2, v___y_556_);
lean_ctor_set(v___x_557_, 3, v___y_555_);
v___x_558_ = lean_st_ref_put(v_a_298_, v___x_557_);
v___x_559_ = lean_st_ref_get(v_a_298_);
v_incTotal_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc_ref(v_incTotal_560_);
v_incAccum_561_ = lean_ctor_get(v___x_559_, 2);
lean_inc_ref(v_incAccum_561_);
lean_dec(v___x_559_);
v___x_562_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2(v_incAccum_561_, v_fvarId_543_);
lean_dec_ref(v_incAccum_561_);
v___x_563_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2(v_incTotal_560_, v_fvarId_543_);
lean_dec_ref(v_incTotal_560_);
v___x_564_ = lean_nat_dec_eq(v___x_562_, v___x_563_);
lean_dec(v___x_562_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
lean_dec(v___x_563_);
lean_del_object(v___x_549_);
lean_dec(v_fvarId_543_);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___y_553_);
return v___x_565_;
}
else
{
lean_object* v___x_567_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 2, v___y_553_);
lean_ctor_set(v___x_549_, 1, v___x_563_);
v___x_567_ = v___x_549_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_fvarId_543_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v___y_553_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*3, v_check_545_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*3 + 1, v_persistent_546_);
v___x_567_ = v_reuseFailAlloc_569_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
}
v___jp_570_:
{
lean_object* v_size_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_size_578_ = lean_ctor_get(v___y_575_, 0);
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_add(v_size_578_, v___x_579_);
lean_inc(v_fvarId_543_);
v___x_581_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_575_, v___x_580_, v_i_577_, v_fvarId_543_, v___y_576_);
lean_dec(v_i_577_);
v___y_552_ = v___y_571_;
v___y_553_ = v___y_572_;
v___y_554_ = v___y_573_;
v___y_555_ = v___y_574_;
v___y_556_ = v___x_581_;
goto v___jp_551_;
}
v___jp_582_:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v___y_586_);
lean_dec_ref(v___y_586_);
v___x_590_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v___x_589_, v_fvarId_543_);
switch(lean_obj_tag(v___x_590_))
{
case 0:
{
lean_object* v_index_591_; lean_object* v_size_592_; lean_object* v___x_593_; 
v_index_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_index_591_);
lean_dec_ref_known(v___x_590_, 3);
v_size_592_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_size_592_);
lean_inc(v_fvarId_543_);
v___x_593_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_589_, v_size_592_, v_index_591_, v_fvarId_543_, v___y_588_);
lean_dec(v_index_591_);
v___y_552_ = v___y_583_;
v___y_553_ = v___y_584_;
v___y_554_ = v___y_585_;
v___y_555_ = v___y_587_;
v___y_556_ = v___x_593_;
goto v___jp_551_;
}
case 1:
{
lean_object* v_index_594_; 
v_index_594_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_index_594_);
lean_dec_ref_known(v___x_590_, 1);
v___y_571_ = v___y_583_;
v___y_572_ = v___y_584_;
v___y_573_ = v___y_585_;
v___y_574_ = v___y_587_;
v___y_575_ = v___x_589_;
v___y_576_ = v___y_588_;
v_i_577_ = v_index_594_;
goto v___jp_570_;
}
default: 
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_589_, v___x_595_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_index_597_; 
v_index_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_index_597_);
lean_dec_ref_known(v___x_596_, 1);
v___y_571_ = v___y_583_;
v___y_572_ = v___y_584_;
v___y_573_ = v___y_585_;
v___y_574_ = v___y_587_;
v___y_575_ = v___x_589_;
v___y_576_ = v___y_588_;
v_i_577_ = v_index_597_;
goto v___jp_570_;
}
else
{
lean_dec(v___y_588_);
v___y_552_ = v___y_583_;
v___y_553_ = v___y_584_;
v___y_554_ = v___y_585_;
v___y_555_ = v___y_587_;
v___y_556_ = v___x_589_;
goto v___jp_551_;
}
}
}
}
v___jp_598_:
{
lean_object* v_size_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_size_606_ = lean_ctor_get(v___y_601_, 0);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = lean_nat_add(v_size_606_, v___x_607_);
lean_inc(v_fvarId_543_);
v___x_609_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_601_, v___x_608_, v_i_605_, v_fvarId_543_, v___y_603_);
lean_dec(v_i_605_);
v___y_552_ = v___y_599_;
v___y_553_ = v___y_600_;
v___y_554_ = v___y_602_;
v___y_555_ = v___y_604_;
v___y_556_ = v___x_609_;
goto v___jp_551_;
}
v___jp_610_:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v___y_616_, v_fvarId_543_);
switch(lean_obj_tag(v___x_617_))
{
case 0:
{
lean_object* v_index_618_; lean_object* v_size_619_; lean_object* v___x_620_; 
v_index_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_index_618_);
lean_dec_ref_known(v___x_617_, 3);
v_size_619_ = lean_ctor_get(v___y_616_, 0);
lean_inc(v_size_619_);
lean_inc(v_fvarId_543_);
v___x_620_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_616_, v_size_619_, v_index_618_, v_fvarId_543_, v___y_614_);
lean_dec(v_index_618_);
v___y_552_ = v___y_611_;
v___y_553_ = v___y_612_;
v___y_554_ = v___y_613_;
v___y_555_ = v___y_615_;
v___y_556_ = v___x_620_;
goto v___jp_551_;
}
case 1:
{
lean_object* v_index_621_; 
v_index_621_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_index_621_);
lean_dec_ref_known(v___x_617_, 1);
v___y_599_ = v___y_611_;
v___y_600_ = v___y_612_;
v___y_601_ = v___y_616_;
v___y_602_ = v___y_613_;
v___y_603_ = v___y_614_;
v___y_604_ = v___y_615_;
v_i_605_ = v_index_621_;
goto v___jp_598_;
}
default: 
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_616_, v___x_622_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_index_624_; 
v_index_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_index_624_);
lean_dec_ref_known(v___x_623_, 1);
v___y_599_ = v___y_611_;
v___y_600_ = v___y_612_;
v___y_601_ = v___y_616_;
v___y_602_ = v___y_613_;
v___y_603_ = v___y_614_;
v___y_604_ = v___y_615_;
v_i_605_ = v_index_624_;
goto v___jp_598_;
}
else
{
lean_dec(v___y_614_);
v___y_552_ = v___y_611_;
v___y_553_ = v___y_612_;
v___y_554_ = v___y_613_;
v___y_555_ = v___y_615_;
v___y_556_ = v___y_616_;
goto v___jp_551_;
}
}
}
}
v_resetjp_630_:
{
lean_object* v___y_634_; lean_object* v___x_696_; 
v___x_696_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v_incTotal_626_, v_fvarId_543_);
switch(lean_obj_tag(v___x_696_))
{
case 0:
{
lean_object* v_index_697_; lean_object* v_value_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_index_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_index_697_);
v_value_698_ = lean_ctor_get(v___x_696_, 2);
lean_inc(v_value_698_);
lean_dec_ref_known(v___x_696_, 3);
v___x_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_699_, 0, v_value_698_);
v___x_700_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0(v_n_544_, v___x_699_);
lean_dec_ref_known(v___x_699_, 1);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_size_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_size_701_ = lean_ctor_get(v_incTotal_626_, 0);
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = lean_nat_sub(v_size_701_, v___x_702_);
v___x_704_ = l_Std_DHashMap_Raw_clearCell___redArg(v_incTotal_626_, v___x_703_, v_index_697_);
lean_dec(v_index_697_);
v___y_634_ = v___x_704_;
goto v___jp_633_;
}
else
{
lean_object* v_val_705_; lean_object* v_size_706_; lean_object* v___x_707_; 
v_val_705_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_val_705_);
lean_dec_ref_known(v___x_700_, 1);
v_size_706_ = lean_ctor_get(v_incTotal_626_, 0);
lean_inc(v_size_706_);
lean_inc(v_fvarId_543_);
v___x_707_ = l_Std_DHashMap_Raw_setEntry___redArg(v_incTotal_626_, v_size_706_, v_index_697_, v_fvarId_543_, v_val_705_);
lean_dec(v_index_697_);
v___y_634_ = v___x_707_;
goto v___jp_633_;
}
}
case 1:
{
lean_object* v_index_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_index_708_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_index_708_);
lean_dec_ref_known(v___x_696_, 1);
v___x_709_ = lean_box(0);
v___x_710_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0(v_n_544_, v___x_709_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_dec(v_index_708_);
v___y_634_ = v_incTotal_626_;
goto v___jp_633_;
}
else
{
lean_object* v_val_711_; lean_object* v___y_713_; lean_object* v_i_714_; lean_object* v_size_729_; lean_object* v_keyArray_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v_val_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_val_711_);
lean_dec_ref_known(v___x_710_, 1);
v_size_729_ = lean_ctor_get(v_incTotal_626_, 0);
v_keyArray_730_ = lean_ctor_get(v_incTotal_626_, 1);
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = lean_nat_add(v_size_729_, v___x_731_);
v___x_733_ = lean_array_get_size(v_keyArray_730_);
v___x_734_ = lean_nat_dec_lt(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_dec(v___x_732_);
lean_dec(v_index_708_);
goto v___jp_719_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_735_ = lean_unsigned_to_nat(4u);
v___x_736_ = lean_nat_mul(v___x_732_, v___x_735_);
v___x_737_ = lean_unsigned_to_nat(3u);
v___x_738_ = lean_nat_mul(v___x_733_, v___x_737_);
v___x_739_ = lean_nat_dec_le(v___x_736_, v___x_738_);
lean_dec(v___x_738_);
lean_dec(v___x_736_);
if (v___x_739_ == 0)
{
lean_dec(v___x_732_);
lean_dec(v_index_708_);
goto v___jp_719_;
}
else
{
lean_object* v___x_740_; 
lean_inc(v_fvarId_543_);
v___x_740_ = l_Std_DHashMap_Raw_setEntry___redArg(v_incTotal_626_, v___x_732_, v_index_708_, v_fvarId_543_, v_val_711_);
lean_dec(v_index_708_);
v___y_634_ = v___x_740_;
goto v___jp_633_;
}
}
v___jp_712_:
{
lean_object* v_size_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_size_715_ = lean_ctor_get(v___y_713_, 0);
v___x_716_ = lean_unsigned_to_nat(1u);
v___x_717_ = lean_nat_add(v_size_715_, v___x_716_);
lean_inc(v_fvarId_543_);
v___x_718_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_713_, v___x_717_, v_i_714_, v_fvarId_543_, v_val_711_);
lean_dec(v_i_714_);
v___y_634_ = v___x_718_;
goto v___jp_633_;
}
v___jp_719_:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_incTotal_626_);
lean_dec_ref(v_incTotal_626_);
v___x_721_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v___x_720_, v_fvarId_543_);
switch(lean_obj_tag(v___x_721_))
{
case 0:
{
lean_object* v_index_722_; lean_object* v_size_723_; lean_object* v___x_724_; 
v_index_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_index_722_);
lean_dec_ref_known(v___x_721_, 3);
v_size_723_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_size_723_);
lean_inc(v_fvarId_543_);
v___x_724_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_720_, v_size_723_, v_index_722_, v_fvarId_543_, v_val_711_);
lean_dec(v_index_722_);
v___y_634_ = v___x_724_;
goto v___jp_633_;
}
case 1:
{
lean_object* v_index_725_; 
v_index_725_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_index_725_);
lean_dec_ref_known(v___x_721_, 1);
v___y_713_ = v___x_720_;
v_i_714_ = v_index_725_;
goto v___jp_712_;
}
default: 
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_720_, v___x_726_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_index_728_; 
v_index_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_index_728_);
lean_dec_ref_known(v___x_727_, 1);
v___y_713_ = v___x_720_;
v_i_714_ = v_index_728_;
goto v___jp_712_;
}
else
{
lean_dec(v_val_711_);
v___y_634_ = v___x_720_;
goto v___jp_633_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_box(0);
v___x_742_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0(v_n_544_, v___x_741_);
if (lean_obj_tag(v___x_742_) == 0)
{
v___y_634_ = v_incTotal_626_;
goto v___jp_633_;
}
else
{
lean_object* v_val_743_; lean_object* v___y_745_; lean_object* v_i_746_; lean_object* v___y_752_; lean_object* v_size_761_; lean_object* v_keyArray_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_val_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_val_743_);
lean_dec_ref_known(v___x_742_, 1);
v_size_761_ = lean_ctor_get(v_incTotal_626_, 0);
v_keyArray_762_ = lean_ctor_get(v_incTotal_626_, 1);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v_size_761_, v___x_763_);
v___x_765_ = lean_array_get_size(v_keyArray_762_);
v___x_766_ = lean_nat_dec_lt(v___x_764_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
lean_dec(v___x_764_);
v___x_767_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_incTotal_626_);
lean_dec_ref(v_incTotal_626_);
v___y_752_ = v___x_767_;
goto v___jp_751_;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_768_ = lean_unsigned_to_nat(4u);
v___x_769_ = lean_nat_mul(v___x_764_, v___x_768_);
lean_dec(v___x_764_);
v___x_770_ = lean_unsigned_to_nat(3u);
v___x_771_ = lean_nat_mul(v___x_765_, v___x_770_);
v___x_772_ = lean_nat_dec_le(v___x_769_, v___x_771_);
lean_dec(v___x_771_);
lean_dec(v___x_769_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_incTotal_626_);
lean_dec_ref(v_incTotal_626_);
v___y_752_ = v___x_773_;
goto v___jp_751_;
}
else
{
v___y_752_ = v_incTotal_626_;
goto v___jp_751_;
}
}
v___jp_744_:
{
lean_object* v_size_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_size_747_ = lean_ctor_get(v___y_745_, 0);
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_nat_add(v_size_747_, v___x_748_);
lean_inc(v_fvarId_543_);
v___x_750_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_745_, v___x_749_, v_i_746_, v_fvarId_543_, v_val_743_);
lean_dec(v_i_746_);
v___y_634_ = v___x_750_;
goto v___jp_633_;
}
v___jp_751_:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v___y_752_, v_fvarId_543_);
switch(lean_obj_tag(v___x_753_))
{
case 0:
{
lean_object* v_index_754_; lean_object* v_size_755_; lean_object* v___x_756_; 
v_index_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_index_754_);
lean_dec_ref_known(v___x_753_, 3);
v_size_755_ = lean_ctor_get(v___y_752_, 0);
lean_inc(v_size_755_);
lean_inc(v_fvarId_543_);
v___x_756_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_752_, v_size_755_, v_index_754_, v_fvarId_543_, v_val_743_);
lean_dec(v_index_754_);
v___y_634_ = v___x_756_;
goto v___jp_633_;
}
case 1:
{
lean_object* v_index_757_; 
v_index_757_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_index_757_);
lean_dec_ref_known(v___x_753_, 1);
v___y_745_ = v___y_752_;
v_i_746_ = v_index_757_;
goto v___jp_744_;
}
default: 
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_752_, v___x_758_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_index_760_; 
v_index_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_index_760_);
lean_dec_ref_known(v___x_759_, 1);
v___y_745_ = v___y_752_;
v_i_746_ = v_index_760_;
goto v___jp_744_;
}
else
{
lean_dec(v_val_743_);
v___y_634_ = v___y_752_;
goto v___jp_633_;
}
}
}
}
}
}
}
v___jp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___y_634_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___y_634_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_decTotal_627_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_incAccum_628_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_decPlaced_629_);
v___x_636_ = v_reuseFailAlloc_695_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_st_ref_put(v_a_298_, v___x_636_);
v___x_638_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_547_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_694_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_694_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_694_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_694_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v_incTotal_644_; lean_object* v_decTotal_645_; lean_object* v_incAccum_646_; lean_object* v_decPlaced_647_; lean_object* v___x_648_; 
v___x_643_ = lean_st_ref_take(v_a_298_);
v_incTotal_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc_ref(v_incTotal_644_);
v_decTotal_645_ = lean_ctor_get(v___x_643_, 1);
lean_inc_ref(v_decTotal_645_);
v_incAccum_646_ = lean_ctor_get(v___x_643_, 2);
lean_inc_ref(v_incAccum_646_);
v_decPlaced_647_ = lean_ctor_get(v___x_643_, 3);
lean_inc_ref(v_decPlaced_647_);
lean_dec(v___x_643_);
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v_incAccum_646_, v_fvarId_543_);
switch(lean_obj_tag(v___x_648_))
{
case 0:
{
lean_object* v_index_649_; lean_object* v_value_650_; lean_object* v___x_652_; 
v_index_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_index_649_);
v_value_650_ = lean_ctor_get(v___x_648_, 2);
lean_inc(v_value_650_);
lean_dec_ref_known(v___x_648_, 3);
if (v_isShared_642_ == 0)
{
lean_ctor_set_tag(v___x_641_, 1);
lean_ctor_set(v___x_641_, 0, v_value_650_);
v___x_652_ = v___x_641_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_value_650_);
v___x_652_ = v_reuseFailAlloc_661_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; 
v___x_653_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0(v_n_544_, v___x_652_);
lean_dec_ref(v___x_652_);
lean_dec(v_n_544_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_size_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_size_654_ = lean_ctor_get(v_incAccum_646_, 0);
v___x_655_ = lean_unsigned_to_nat(1u);
v___x_656_ = lean_nat_sub(v_size_654_, v___x_655_);
v___x_657_ = l_Std_DHashMap_Raw_clearCell___redArg(v_incAccum_646_, v___x_656_, v_index_649_);
lean_dec(v_index_649_);
v___y_552_ = v_incTotal_644_;
v___y_553_ = v_a_639_;
v___y_554_ = v_decTotal_645_;
v___y_555_ = v_decPlaced_647_;
v___y_556_ = v___x_657_;
goto v___jp_551_;
}
else
{
lean_object* v_val_658_; lean_object* v_size_659_; lean_object* v___x_660_; 
v_val_658_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_val_658_);
lean_dec_ref_known(v___x_653_, 1);
v_size_659_ = lean_ctor_get(v_incAccum_646_, 0);
lean_inc(v_size_659_);
lean_inc(v_fvarId_543_);
v___x_660_ = l_Std_DHashMap_Raw_setEntry___redArg(v_incAccum_646_, v_size_659_, v_index_649_, v_fvarId_543_, v_val_658_);
lean_dec(v_index_649_);
v___y_552_ = v_incTotal_644_;
v___y_553_ = v_a_639_;
v___y_554_ = v_decTotal_645_;
v___y_555_ = v_decPlaced_647_;
v___y_556_ = v___x_660_;
goto v___jp_551_;
}
}
}
case 1:
{
lean_object* v_index_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
lean_del_object(v___x_641_);
v_index_662_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_index_662_);
lean_dec_ref_known(v___x_648_, 1);
v___x_663_ = lean_box(0);
v___x_664_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0(v_n_544_, v___x_663_);
lean_dec(v_n_544_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_dec(v_index_662_);
v___y_552_ = v_incTotal_644_;
v___y_553_ = v_a_639_;
v___y_554_ = v_decTotal_645_;
v___y_555_ = v_decPlaced_647_;
v___y_556_ = v_incAccum_646_;
goto v___jp_551_;
}
else
{
lean_object* v_val_665_; lean_object* v_size_666_; lean_object* v_keyArray_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_val_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_val_665_);
lean_dec_ref_known(v___x_664_, 1);
v_size_666_ = lean_ctor_get(v_incAccum_646_, 0);
v_keyArray_667_ = lean_ctor_get(v_incAccum_646_, 1);
v___x_668_ = lean_unsigned_to_nat(1u);
v___x_669_ = lean_nat_add(v_size_666_, v___x_668_);
v___x_670_ = lean_array_get_size(v_keyArray_667_);
v___x_671_ = lean_nat_dec_lt(v___x_669_, v___x_670_);
if (v___x_671_ == 0)
{
lean_dec(v___x_669_);
lean_dec(v_index_662_);
v___y_583_ = v_incTotal_644_;
v___y_584_ = v_a_639_;
v___y_585_ = v_decTotal_645_;
v___y_586_ = v_incAccum_646_;
v___y_587_ = v_decPlaced_647_;
v___y_588_ = v_val_665_;
goto v___jp_582_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_672_ = lean_unsigned_to_nat(4u);
v___x_673_ = lean_nat_mul(v___x_669_, v___x_672_);
v___x_674_ = lean_unsigned_to_nat(3u);
v___x_675_ = lean_nat_mul(v___x_670_, v___x_674_);
v___x_676_ = lean_nat_dec_le(v___x_673_, v___x_675_);
lean_dec(v___x_675_);
lean_dec(v___x_673_);
if (v___x_676_ == 0)
{
lean_dec(v___x_669_);
lean_dec(v_index_662_);
v___y_583_ = v_incTotal_644_;
v___y_584_ = v_a_639_;
v___y_585_ = v_decTotal_645_;
v___y_586_ = v_incAccum_646_;
v___y_587_ = v_decPlaced_647_;
v___y_588_ = v_val_665_;
goto v___jp_582_;
}
else
{
lean_object* v___x_677_; 
lean_inc(v_fvarId_543_);
v___x_677_ = l_Std_DHashMap_Raw_setEntry___redArg(v_incAccum_646_, v___x_669_, v_index_662_, v_fvarId_543_, v_val_665_);
lean_dec(v_index_662_);
v___y_552_ = v_incTotal_644_;
v___y_553_ = v_a_639_;
v___y_554_ = v_decTotal_645_;
v___y_555_ = v_decPlaced_647_;
v___y_556_ = v___x_677_;
goto v___jp_551_;
}
}
}
}
default: 
{
lean_object* v___x_678_; lean_object* v___x_679_; 
lean_del_object(v___x_641_);
v___x_678_ = lean_box(0);
v___x_679_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0(v_n_544_, v___x_678_);
lean_dec(v_n_544_);
if (lean_obj_tag(v___x_679_) == 0)
{
v___y_552_ = v_incTotal_644_;
v___y_553_ = v_a_639_;
v___y_554_ = v_decTotal_645_;
v___y_555_ = v_decPlaced_647_;
v___y_556_ = v_incAccum_646_;
goto v___jp_551_;
}
else
{
lean_object* v_val_680_; lean_object* v_size_681_; lean_object* v_keyArray_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_val_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_val_680_);
lean_dec_ref_known(v___x_679_, 1);
v_size_681_ = lean_ctor_get(v_incAccum_646_, 0);
v_keyArray_682_ = lean_ctor_get(v_incAccum_646_, 1);
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_nat_add(v_size_681_, v___x_683_);
v___x_685_ = lean_array_get_size(v_keyArray_682_);
v___x_686_ = lean_nat_dec_lt(v___x_684_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
lean_dec(v___x_684_);
v___x_687_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_incAccum_646_);
lean_dec_ref(v_incAccum_646_);
v___y_611_ = v_incTotal_644_;
v___y_612_ = v_a_639_;
v___y_613_ = v_decTotal_645_;
v___y_614_ = v_val_680_;
v___y_615_ = v_decPlaced_647_;
v___y_616_ = v___x_687_;
goto v___jp_610_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_688_ = lean_unsigned_to_nat(4u);
v___x_689_ = lean_nat_mul(v___x_684_, v___x_688_);
lean_dec(v___x_684_);
v___x_690_ = lean_unsigned_to_nat(3u);
v___x_691_ = lean_nat_mul(v___x_685_, v___x_690_);
v___x_692_ = lean_nat_dec_le(v___x_689_, v___x_691_);
lean_dec(v___x_691_);
lean_dec(v___x_689_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_incAccum_646_);
lean_dec_ref(v_incAccum_646_);
v___y_611_ = v_incTotal_644_;
v___y_612_ = v_a_639_;
v___y_613_ = v_decTotal_645_;
v___y_614_ = v_val_680_;
v___y_615_ = v_decPlaced_647_;
v___y_616_ = v___x_693_;
goto v___jp_610_;
}
else
{
v___y_611_ = v_incTotal_644_;
v___y_612_ = v_a_639_;
v___y_613_ = v_decTotal_645_;
v___y_614_ = v_val_680_;
v___y_615_ = v_decPlaced_647_;
v___y_616_ = v_incAccum_646_;
goto v___jp_610_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_549_);
lean_dec(v_n_544_);
lean_dec(v_fvarId_543_);
return v___x_638_;
}
}
}
}
}
}
case 12:
{
lean_object* v_fvarId_776_; lean_object* v_n_777_; uint8_t v_check_778_; uint8_t v_persistent_779_; lean_object* v_objs_x3f_780_; lean_object* v_k_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_997_; 
v_fvarId_776_ = lean_ctor_get(v_code_297_, 0);
v_n_777_ = lean_ctor_get(v_code_297_, 1);
v_check_778_ = lean_ctor_get_uint8(v_code_297_, sizeof(void*)*4);
v_persistent_779_ = lean_ctor_get_uint8(v_code_297_, sizeof(void*)*4 + 1);
v_objs_x3f_780_ = lean_ctor_get(v_code_297_, 2);
v_k_781_ = lean_ctor_get(v_code_297_, 3);
v_isSharedCheck_997_ = !lean_is_exclusive(v_code_297_);
if (v_isSharedCheck_997_ == 0)
{
v___x_783_ = v_code_297_;
v_isShared_784_ = v_isSharedCheck_997_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_k_781_);
lean_inc(v_objs_x3f_780_);
lean_inc(v_n_777_);
lean_inc(v_fvarId_776_);
lean_dec(v_code_297_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_997_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v_i_807_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v_i_836_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___x_858_; lean_object* v_incTotal_859_; lean_object* v_decTotal_860_; lean_object* v_incAccum_861_; lean_object* v_decPlaced_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_996_; 
v___x_858_ = lean_st_ref_take(v_a_298_);
v_incTotal_859_ = lean_ctor_get(v___x_858_, 0);
v_decTotal_860_ = lean_ctor_get(v___x_858_, 1);
v_incAccum_861_ = lean_ctor_get(v___x_858_, 2);
v_decPlaced_862_ = lean_ctor_get(v___x_858_, 3);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_996_ == 0)
{
v___x_864_ = v___x_858_;
v_isShared_865_ = v_isSharedCheck_996_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_decPlaced_862_);
lean_inc(v_incAccum_861_);
lean_inc(v_decTotal_860_);
lean_inc(v_incTotal_859_);
lean_dec(v___x_858_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_996_;
goto v_resetjp_863_;
}
v___jp_785_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_792_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_792_, 0, v___y_788_);
lean_ctor_set(v___x_792_, 1, v___y_787_);
lean_ctor_set(v___x_792_, 2, v___y_786_);
lean_ctor_set(v___x_792_, 3, v___y_791_);
v___x_793_ = lean_st_ref_put(v_a_298_, v___x_792_);
v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2(v___y_789_, v_fvarId_776_);
lean_dec_ref(v___y_789_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 3, v___y_790_);
lean_ctor_set(v___x_783_, 1, v___x_794_);
v___x_796_ = v___x_783_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_fvarId_776_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_objs_x3f_780_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v___y_790_);
lean_ctor_set_uint8(v_reuseFailAlloc_798_, sizeof(void*)*4, v_check_778_);
lean_ctor_set_uint8(v_reuseFailAlloc_798_, sizeof(void*)*4 + 1, v_persistent_779_);
v___x_796_ = v_reuseFailAlloc_798_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; 
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
v___jp_799_:
{
lean_object* v_size_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_size_808_ = lean_ctor_get(v___y_805_, 0);
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_add(v_size_808_, v___x_809_);
lean_inc(v_fvarId_776_);
v___x_811_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_805_, v___x_810_, v_i_807_, v_fvarId_776_, v___y_804_);
lean_dec(v_i_807_);
v___y_786_ = v___y_800_;
v___y_787_ = v___y_801_;
v___y_788_ = v___y_802_;
v___y_789_ = v___y_803_;
v___y_790_ = v___y_806_;
v___y_791_ = v___x_811_;
goto v___jp_785_;
}
v___jp_812_:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v___y_819_, v_fvarId_776_);
switch(lean_obj_tag(v___x_820_))
{
case 0:
{
lean_object* v_index_821_; lean_object* v_size_822_; lean_object* v___x_823_; 
v_index_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_index_821_);
lean_dec_ref_known(v___x_820_, 3);
v_size_822_ = lean_ctor_get(v___y_819_, 0);
lean_inc(v_size_822_);
lean_inc(v_fvarId_776_);
v___x_823_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_819_, v_size_822_, v_index_821_, v_fvarId_776_, v___y_817_);
lean_dec(v_index_821_);
v___y_786_ = v___y_813_;
v___y_787_ = v___y_814_;
v___y_788_ = v___y_815_;
v___y_789_ = v___y_816_;
v___y_790_ = v___y_818_;
v___y_791_ = v___x_823_;
goto v___jp_785_;
}
case 1:
{
lean_object* v_index_824_; 
v_index_824_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_index_824_);
lean_dec_ref_known(v___x_820_, 1);
v___y_800_ = v___y_813_;
v___y_801_ = v___y_814_;
v___y_802_ = v___y_815_;
v___y_803_ = v___y_816_;
v___y_804_ = v___y_817_;
v___y_805_ = v___y_819_;
v___y_806_ = v___y_818_;
v_i_807_ = v_index_824_;
goto v___jp_799_;
}
default: 
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_819_, v___x_825_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_index_827_; 
v_index_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_index_827_);
lean_dec_ref_known(v___x_826_, 1);
v___y_800_ = v___y_813_;
v___y_801_ = v___y_814_;
v___y_802_ = v___y_815_;
v___y_803_ = v___y_816_;
v___y_804_ = v___y_817_;
v___y_805_ = v___y_819_;
v___y_806_ = v___y_818_;
v_i_807_ = v_index_827_;
goto v___jp_799_;
}
else
{
v___y_786_ = v___y_813_;
v___y_787_ = v___y_814_;
v___y_788_ = v___y_815_;
v___y_789_ = v___y_816_;
v___y_790_ = v___y_818_;
v___y_791_ = v___y_819_;
goto v___jp_785_;
}
}
}
}
v___jp_828_:
{
lean_object* v_size_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_size_837_ = lean_ctor_get(v___y_835_, 0);
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = lean_nat_add(v_size_837_, v___x_838_);
lean_inc(v_fvarId_776_);
v___x_840_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_835_, v___x_839_, v_i_836_, v_fvarId_776_, v___y_833_);
lean_dec(v_i_836_);
v___y_786_ = v___y_829_;
v___y_787_ = v___y_830_;
v___y_788_ = v___y_831_;
v___y_789_ = v___y_832_;
v___y_790_ = v___y_834_;
v___y_791_ = v___x_840_;
goto v___jp_785_;
}
v___jp_841_:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v___y_845_);
lean_dec_ref(v___y_845_);
v___x_850_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v___x_849_, v_fvarId_776_);
switch(lean_obj_tag(v___x_850_))
{
case 0:
{
lean_object* v_index_851_; lean_object* v_size_852_; lean_object* v___x_853_; 
v_index_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_index_851_);
lean_dec_ref_known(v___x_850_, 3);
v_size_852_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_size_852_);
lean_inc(v_fvarId_776_);
v___x_853_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_849_, v_size_852_, v_index_851_, v_fvarId_776_, v___y_847_);
lean_dec(v_index_851_);
v___y_786_ = v___y_842_;
v___y_787_ = v___y_843_;
v___y_788_ = v___y_844_;
v___y_789_ = v___y_846_;
v___y_790_ = v___y_848_;
v___y_791_ = v___x_853_;
goto v___jp_785_;
}
case 1:
{
lean_object* v_index_854_; 
v_index_854_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_index_854_);
lean_dec_ref_known(v___x_850_, 1);
v___y_829_ = v___y_842_;
v___y_830_ = v___y_843_;
v___y_831_ = v___y_844_;
v___y_832_ = v___y_846_;
v___y_833_ = v___y_847_;
v___y_834_ = v___y_848_;
v___y_835_ = v___x_849_;
v_i_836_ = v_index_854_;
goto v___jp_828_;
}
default: 
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_849_, v___x_855_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_index_857_; 
v_index_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_index_857_);
lean_dec_ref_known(v___x_856_, 1);
v___y_829_ = v___y_842_;
v___y_830_ = v___y_843_;
v___y_831_ = v___y_844_;
v___y_832_ = v___y_846_;
v___y_833_ = v___y_847_;
v___y_834_ = v___y_848_;
v___y_835_ = v___x_849_;
v_i_836_ = v_index_857_;
goto v___jp_828_;
}
else
{
v___y_786_ = v___y_842_;
v___y_787_ = v___y_843_;
v___y_788_ = v___y_844_;
v___y_789_ = v___y_846_;
v___y_790_ = v___y_848_;
v___y_791_ = v___x_849_;
goto v___jp_785_;
}
}
}
}
v_resetjp_863_:
{
lean_object* v___y_867_; lean_object* v___x_918_; 
v___x_918_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v_decTotal_860_, v_fvarId_776_);
switch(lean_obj_tag(v___x_918_))
{
case 0:
{
lean_object* v_index_919_; lean_object* v_value_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_index_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_index_919_);
v_value_920_ = lean_ctor_get(v___x_918_, 2);
lean_inc(v_value_920_);
lean_dec_ref_known(v___x_918_, 3);
v___x_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_921_, 0, v_value_920_);
v___x_922_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0(v_n_777_, v___x_921_);
lean_dec_ref_known(v___x_921_, 1);
lean_dec(v_n_777_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_size_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_size_923_ = lean_ctor_get(v_decTotal_860_, 0);
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_sub(v_size_923_, v___x_924_);
v___x_926_ = l_Std_DHashMap_Raw_clearCell___redArg(v_decTotal_860_, v___x_925_, v_index_919_);
lean_dec(v_index_919_);
v___y_867_ = v___x_926_;
goto v___jp_866_;
}
else
{
lean_object* v_val_927_; lean_object* v_size_928_; lean_object* v___x_929_; 
v_val_927_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_val_927_);
lean_dec_ref_known(v___x_922_, 1);
v_size_928_ = lean_ctor_get(v_decTotal_860_, 0);
lean_inc(v_size_928_);
lean_inc(v_fvarId_776_);
v___x_929_ = l_Std_DHashMap_Raw_setEntry___redArg(v_decTotal_860_, v_size_928_, v_index_919_, v_fvarId_776_, v_val_927_);
lean_dec(v_index_919_);
v___y_867_ = v___x_929_;
goto v___jp_866_;
}
}
case 1:
{
lean_object* v_index_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_index_930_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_index_930_);
lean_dec_ref_known(v___x_918_, 1);
v___x_931_ = lean_box(0);
v___x_932_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0(v_n_777_, v___x_931_);
lean_dec(v_n_777_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_dec(v_index_930_);
v___y_867_ = v_decTotal_860_;
goto v___jp_866_;
}
else
{
lean_object* v_val_933_; lean_object* v___y_935_; lean_object* v_i_936_; lean_object* v_size_951_; lean_object* v_keyArray_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v_val_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_val_933_);
lean_dec_ref_known(v___x_932_, 1);
v_size_951_ = lean_ctor_get(v_decTotal_860_, 0);
v_keyArray_952_ = lean_ctor_get(v_decTotal_860_, 1);
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_add(v_size_951_, v___x_953_);
v___x_955_ = lean_array_get_size(v_keyArray_952_);
v___x_956_ = lean_nat_dec_lt(v___x_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_dec(v___x_954_);
lean_dec(v_index_930_);
goto v___jp_941_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_957_ = lean_unsigned_to_nat(4u);
v___x_958_ = lean_nat_mul(v___x_954_, v___x_957_);
v___x_959_ = lean_unsigned_to_nat(3u);
v___x_960_ = lean_nat_mul(v___x_955_, v___x_959_);
v___x_961_ = lean_nat_dec_le(v___x_958_, v___x_960_);
lean_dec(v___x_960_);
lean_dec(v___x_958_);
if (v___x_961_ == 0)
{
lean_dec(v___x_954_);
lean_dec(v_index_930_);
goto v___jp_941_;
}
else
{
lean_object* v___x_962_; 
lean_inc(v_fvarId_776_);
v___x_962_ = l_Std_DHashMap_Raw_setEntry___redArg(v_decTotal_860_, v___x_954_, v_index_930_, v_fvarId_776_, v_val_933_);
lean_dec(v_index_930_);
v___y_867_ = v___x_962_;
goto v___jp_866_;
}
}
v___jp_934_:
{
lean_object* v_size_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_size_937_ = lean_ctor_get(v___y_935_, 0);
v___x_938_ = lean_unsigned_to_nat(1u);
v___x_939_ = lean_nat_add(v_size_937_, v___x_938_);
lean_inc(v_fvarId_776_);
v___x_940_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_935_, v___x_939_, v_i_936_, v_fvarId_776_, v_val_933_);
lean_dec(v_i_936_);
v___y_867_ = v___x_940_;
goto v___jp_866_;
}
v___jp_941_:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_decTotal_860_);
lean_dec_ref(v_decTotal_860_);
v___x_943_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v___x_942_, v_fvarId_776_);
switch(lean_obj_tag(v___x_943_))
{
case 0:
{
lean_object* v_index_944_; lean_object* v_size_945_; lean_object* v___x_946_; 
v_index_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_index_944_);
lean_dec_ref_known(v___x_943_, 3);
v_size_945_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_size_945_);
lean_inc(v_fvarId_776_);
v___x_946_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_942_, v_size_945_, v_index_944_, v_fvarId_776_, v_val_933_);
lean_dec(v_index_944_);
v___y_867_ = v___x_946_;
goto v___jp_866_;
}
case 1:
{
lean_object* v_index_947_; 
v_index_947_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_index_947_);
lean_dec_ref_known(v___x_943_, 1);
v___y_935_ = v___x_942_;
v_i_936_ = v_index_947_;
goto v___jp_934_;
}
default: 
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_unsigned_to_nat(0u);
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_942_, v___x_948_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_index_950_; 
v_index_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_index_950_);
lean_dec_ref_known(v___x_949_, 1);
v___y_935_ = v___x_942_;
v_i_936_ = v_index_950_;
goto v___jp_934_;
}
else
{
lean_dec(v_val_933_);
v___y_867_ = v___x_942_;
goto v___jp_866_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_box(0);
v___x_964_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___lam__0(v_n_777_, v___x_963_);
lean_dec(v_n_777_);
if (lean_obj_tag(v___x_964_) == 0)
{
v___y_867_ = v_decTotal_860_;
goto v___jp_866_;
}
else
{
lean_object* v_val_965_; lean_object* v___y_967_; lean_object* v_i_968_; lean_object* v___y_974_; lean_object* v_size_983_; lean_object* v_keyArray_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_val_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_val_965_);
lean_dec_ref_known(v___x_964_, 1);
v_size_983_ = lean_ctor_get(v_decTotal_860_, 0);
v_keyArray_984_ = lean_ctor_get(v_decTotal_860_, 1);
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = lean_nat_add(v_size_983_, v___x_985_);
v___x_987_ = lean_array_get_size(v_keyArray_984_);
v___x_988_ = lean_nat_dec_lt(v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
lean_dec(v___x_986_);
v___x_989_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_decTotal_860_);
lean_dec_ref(v_decTotal_860_);
v___y_974_ = v___x_989_;
goto v___jp_973_;
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_990_ = lean_unsigned_to_nat(4u);
v___x_991_ = lean_nat_mul(v___x_986_, v___x_990_);
lean_dec(v___x_986_);
v___x_992_ = lean_unsigned_to_nat(3u);
v___x_993_ = lean_nat_mul(v___x_987_, v___x_992_);
v___x_994_ = lean_nat_dec_le(v___x_991_, v___x_993_);
lean_dec(v___x_993_);
lean_dec(v___x_991_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; 
v___x_995_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_decTotal_860_);
lean_dec_ref(v_decTotal_860_);
v___y_974_ = v___x_995_;
goto v___jp_973_;
}
else
{
v___y_974_ = v_decTotal_860_;
goto v___jp_973_;
}
}
v___jp_966_:
{
lean_object* v_size_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_size_969_ = lean_ctor_get(v___y_967_, 0);
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = lean_nat_add(v_size_969_, v___x_970_);
lean_inc(v_fvarId_776_);
v___x_972_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_967_, v___x_971_, v_i_968_, v_fvarId_776_, v_val_965_);
lean_dec(v_i_968_);
v___y_867_ = v___x_972_;
goto v___jp_866_;
}
v___jp_973_:
{
lean_object* v___x_975_; 
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v___y_974_, v_fvarId_776_);
switch(lean_obj_tag(v___x_975_))
{
case 0:
{
lean_object* v_index_976_; lean_object* v_size_977_; lean_object* v___x_978_; 
v_index_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_index_976_);
lean_dec_ref_known(v___x_975_, 3);
v_size_977_ = lean_ctor_get(v___y_974_, 0);
lean_inc(v_size_977_);
lean_inc(v_fvarId_776_);
v___x_978_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_974_, v_size_977_, v_index_976_, v_fvarId_776_, v_val_965_);
lean_dec(v_index_976_);
v___y_867_ = v___x_978_;
goto v___jp_866_;
}
case 1:
{
lean_object* v_index_979_; 
v_index_979_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_index_979_);
lean_dec_ref_known(v___x_975_, 1);
v___y_967_ = v___y_974_;
v_i_968_ = v_index_979_;
goto v___jp_966_;
}
default: 
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_974_, v___x_980_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_index_982_; 
v_index_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_index_982_);
lean_dec_ref_known(v___x_981_, 1);
v___y_967_ = v___y_974_;
v_i_968_ = v_index_982_;
goto v___jp_966_;
}
else
{
lean_dec(v_val_965_);
v___y_867_ = v___y_974_;
goto v___jp_866_;
}
}
}
}
}
}
}
v___jp_866_:
{
lean_object* v___x_869_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___y_867_);
v___x_869_ = v___x_864_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_incTotal_859_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v___y_867_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_incAccum_861_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v_decPlaced_862_);
v___x_869_ = v_reuseFailAlloc_917_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_st_ref_put(v_a_298_, v___x_869_);
v___x_871_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_781_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_916_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_916_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_916_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_916_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v_decTotal_877_; lean_object* v_decPlaced_878_; uint8_t v___x_879_; 
v___x_876_ = lean_st_ref_get(v_a_298_);
v_decTotal_877_ = lean_ctor_get(v___x_876_, 1);
lean_inc_ref(v_decTotal_877_);
v_decPlaced_878_ = lean_ctor_get(v___x_876_, 3);
lean_inc_ref(v_decPlaced_878_);
lean_dec(v___x_876_);
v___x_879_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5___redArg(v_decPlaced_878_, v_fvarId_776_);
lean_dec_ref(v_decPlaced_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v_incTotal_881_; lean_object* v_decTotal_882_; lean_object* v_incAccum_883_; lean_object* v_decPlaced_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
lean_del_object(v___x_874_);
v___x_880_ = lean_st_ref_take(v_a_298_);
v_incTotal_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc_ref(v_incTotal_881_);
v_decTotal_882_ = lean_ctor_get(v___x_880_, 1);
lean_inc_ref(v_decTotal_882_);
v_incAccum_883_ = lean_ctor_get(v___x_880_, 2);
lean_inc_ref(v_incAccum_883_);
v_decPlaced_884_ = lean_ctor_get(v___x_880_, 3);
lean_inc_ref(v_decPlaced_884_);
lean_dec(v___x_880_);
v___x_885_ = lean_box(0);
v___x_886_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v_decPlaced_884_, v_fvarId_776_);
switch(lean_obj_tag(v___x_886_))
{
case 0:
{
lean_dec_ref_known(v___x_886_, 3);
v___y_786_ = v_incAccum_883_;
v___y_787_ = v_decTotal_882_;
v___y_788_ = v_incTotal_881_;
v___y_789_ = v_decTotal_877_;
v___y_790_ = v_a_872_;
v___y_791_ = v_decPlaced_884_;
goto v___jp_785_;
}
case 1:
{
lean_object* v_index_887_; lean_object* v_size_888_; lean_object* v_keyArray_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v_index_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_index_887_);
lean_dec_ref_known(v___x_886_, 1);
v_size_888_ = lean_ctor_get(v_decPlaced_884_, 0);
v_keyArray_889_ = lean_ctor_get(v_decPlaced_884_, 1);
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = lean_nat_add(v_size_888_, v___x_890_);
v___x_892_ = lean_array_get_size(v_keyArray_889_);
v___x_893_ = lean_nat_dec_lt(v___x_891_, v___x_892_);
if (v___x_893_ == 0)
{
lean_dec(v___x_891_);
lean_dec(v_index_887_);
v___y_842_ = v_incAccum_883_;
v___y_843_ = v_decTotal_882_;
v___y_844_ = v_incTotal_881_;
v___y_845_ = v_decPlaced_884_;
v___y_846_ = v_decTotal_877_;
v___y_847_ = v___x_885_;
v___y_848_ = v_a_872_;
goto v___jp_841_;
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_894_ = lean_unsigned_to_nat(4u);
v___x_895_ = lean_nat_mul(v___x_891_, v___x_894_);
v___x_896_ = lean_unsigned_to_nat(3u);
v___x_897_ = lean_nat_mul(v___x_892_, v___x_896_);
v___x_898_ = lean_nat_dec_le(v___x_895_, v___x_897_);
lean_dec(v___x_897_);
lean_dec(v___x_895_);
if (v___x_898_ == 0)
{
lean_dec(v___x_891_);
lean_dec(v_index_887_);
v___y_842_ = v_incAccum_883_;
v___y_843_ = v_decTotal_882_;
v___y_844_ = v_incTotal_881_;
v___y_845_ = v_decPlaced_884_;
v___y_846_ = v_decTotal_877_;
v___y_847_ = v___x_885_;
v___y_848_ = v_a_872_;
goto v___jp_841_;
}
else
{
lean_object* v___x_899_; 
lean_inc(v_fvarId_776_);
v___x_899_ = l_Std_DHashMap_Raw_setEntry___redArg(v_decPlaced_884_, v___x_891_, v_index_887_, v_fvarId_776_, v___x_885_);
lean_dec(v_index_887_);
v___y_786_ = v_incAccum_883_;
v___y_787_ = v_decTotal_882_;
v___y_788_ = v_incTotal_881_;
v___y_789_ = v_decTotal_877_;
v___y_790_ = v_a_872_;
v___y_791_ = v___x_899_;
goto v___jp_785_;
}
}
}
default: 
{
lean_object* v_size_900_; lean_object* v_keyArray_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_size_900_ = lean_ctor_get(v_decPlaced_884_, 0);
v_keyArray_901_ = lean_ctor_get(v_decPlaced_884_, 1);
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = lean_nat_add(v_size_900_, v___x_902_);
v___x_904_ = lean_array_get_size(v_keyArray_901_);
v___x_905_ = lean_nat_dec_lt(v___x_903_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec(v___x_903_);
v___x_906_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_decPlaced_884_);
lean_dec_ref(v_decPlaced_884_);
v___y_813_ = v_incAccum_883_;
v___y_814_ = v_decTotal_882_;
v___y_815_ = v_incTotal_881_;
v___y_816_ = v_decTotal_877_;
v___y_817_ = v___x_885_;
v___y_818_ = v_a_872_;
v___y_819_ = v___x_906_;
goto v___jp_812_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_907_ = lean_unsigned_to_nat(4u);
v___x_908_ = lean_nat_mul(v___x_903_, v___x_907_);
lean_dec(v___x_903_);
v___x_909_ = lean_unsigned_to_nat(3u);
v___x_910_ = lean_nat_mul(v___x_904_, v___x_909_);
v___x_911_ = lean_nat_dec_le(v___x_908_, v___x_910_);
lean_dec(v___x_910_);
lean_dec(v___x_908_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_decPlaced_884_);
lean_dec_ref(v_decPlaced_884_);
v___y_813_ = v_incAccum_883_;
v___y_814_ = v_decTotal_882_;
v___y_815_ = v_incTotal_881_;
v___y_816_ = v_decTotal_877_;
v___y_817_ = v___x_885_;
v___y_818_ = v_a_872_;
v___y_819_ = v___x_912_;
goto v___jp_812_;
}
else
{
v___y_813_ = v_incAccum_883_;
v___y_814_ = v_decTotal_882_;
v___y_815_ = v_incTotal_881_;
v___y_816_ = v_decTotal_877_;
v___y_817_ = v___x_885_;
v___y_818_ = v_a_872_;
v___y_819_ = v_decPlaced_884_;
goto v___jp_812_;
}
}
}
}
}
else
{
lean_object* v___x_914_; 
lean_dec_ref(v_decTotal_877_);
lean_del_object(v___x_783_);
lean_dec(v_objs_x3f_780_);
lean_dec(v_fvarId_776_);
if (v_isShared_875_ == 0)
{
v___x_914_ = v___x_874_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_872_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_del_object(v___x_783_);
lean_dec(v_objs_x3f_780_);
lean_dec(v_fvarId_776_);
return v___x_871_;
}
}
}
}
}
}
case 13:
{
lean_object* v_fvarId_998_; lean_object* v_k_999_; lean_object* v___x_1000_; 
v_fvarId_998_ = lean_ctor_get(v_code_297_, 0);
v_k_999_ = lean_ctor_get(v_code_297_, 1);
lean_inc_ref(v_k_999_);
v___x_1000_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_999_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1023_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1023_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1023_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
size_t v___x_1005_; size_t v___x_1006_; uint8_t v___x_1007_; 
v___x_1005_ = lean_ptr_addr(v_k_999_);
v___x_1006_ = lean_ptr_addr(v_a_1001_);
v___x_1007_ = lean_usize_dec_eq(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1017_; 
lean_inc(v_fvarId_998_);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_code_297_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; lean_object* v_unused_1019_; 
v_unused_1018_ = lean_ctor_get(v_code_297_, 1);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_code_297_, 0);
lean_dec(v_unused_1019_);
v___x_1009_ = v_code_297_;
v_isShared_1010_ = v_isSharedCheck_1017_;
goto v_resetjp_1008_;
}
else
{
lean_dec(v_code_297_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1017_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v_a_1001_);
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_fvarId_998_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_a_1001_);
v___x_1012_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1012_);
v___x_1014_ = v___x_1003_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v___x_1021_; 
lean_dec(v_a_1001_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v_code_297_);
v___x_1021_ = v___x_1003_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_code_297_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_297_, 2);
return v___x_1000_;
}
}
default: 
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v_code_297_);
return v___x_1024_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC(lean_object* v_code_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__3, &l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__3_once, _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__3);
v___x_1032_ = lean_st_mk_ref(v___x_1031_);
v___x_1033_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_code_1025_, v___x_1032_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1042_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1038_ = lean_st_ref_get(v___x_1032_);
lean_dec(v___x_1032_);
lean_dec(v___x_1038_);
if (v_isShared_1037_ == 0)
{
v___x_1040_ = v___x_1036_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1034_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
else
{
lean_dec(v___x_1032_);
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1___lam__0(lean_object* v_x_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC(v_x_1043_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___boxed(lean_object* v_code_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC(v_code_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1___boxed(lean_object* v_i_1058_, lean_object* v_as_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1(v_i_1058_, v_as_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___boxed(lean_object* v_code_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_code_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0(uint8_t v_pu_1075_, lean_object* v_alt_1076_, lean_object* v_f_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___redArg(v_alt_1076_, v_f_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___boxed(lean_object* v_pu_1085_, lean_object* v_alt_1086_, lean_object* v_f_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
uint8_t v_pu_boxed_1094_; lean_object* v_res_1095_; 
v_pu_boxed_1094_ = lean_unbox(v_pu_1085_);
v_res_1095_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0(v_pu_boxed_1094_, v_alt_1086_, v_f_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3(lean_object* v_00_u03b2_1096_, lean_object* v_m_1097_, lean_object* v_query_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___redArg(v_m_1097_, v_query_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___boxed(lean_object* v_00_u03b2_1100_, lean_object* v_m_1101_, lean_object* v_query_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3(v_00_u03b2_1100_, v_m_1101_, v_query_1102_);
lean_dec(v_query_1102_);
lean_dec_ref(v_m_1101_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4(lean_object* v_00_u03b2_1104_, lean_object* v_m_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_m_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___boxed(lean_object* v_00_u03b2_1107_, lean_object* v_m_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4(v_00_u03b2_1107_, v_m_1108_);
lean_dec_ref(v_m_1108_);
return v_res_1109_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5(lean_object* v_00_u03b2_1110_, lean_object* v_m_1111_, lean_object* v_a_1112_){
_start:
{
uint8_t v___x_1113_; 
v___x_1113_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5___redArg(v_m_1111_, v_a_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5___boxed(lean_object* v_00_u03b2_1114_, lean_object* v_m_1115_, lean_object* v_a_1116_){
_start:
{
uint8_t v_res_1117_; lean_object* v_r_1118_; 
v_res_1117_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5(v_00_u03b2_1114_, v_m_1115_, v_a_1116_);
lean_dec(v_a_1116_);
lean_dec_ref(v_m_1115_);
v_r_1118_ = lean_box(v_res_1117_);
return v_r_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3(lean_object* v_00_u03b2_1119_, lean_object* v_m_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg(v_m_1120_, v_a_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1123_, lean_object* v_m_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3(v_00_u03b2_1123_, v_m_1124_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec_ref(v_m_1124_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__6(lean_object* v_00_u03b2_1127_, lean_object* v_m_1128_, lean_object* v_query_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__6___redArg(v_m_1128_, v_query_1129_, v_x_1130_, v_x_1131_, v_x_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1135_, lean_object* v_m_1136_, lean_object* v_query_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__6(v_00_u03b2_1135_, v_m_1136_, v_query_1137_, v_x_1138_, v_x_1139_, v_x_1140_, v_x_1141_);
lean_dec(v_query_1137_);
lean_dec_ref(v_m_1136_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8(lean_object* v_00_u03b2_1143_, lean_object* v_init_1144_, lean_object* v_b_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8___redArg(v_init_1144_, v_b_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1147_, lean_object* v_init_1148_, lean_object* v_b_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8(v_00_u03b2_1147_, v_init_1148_, v_b_1149_);
lean_dec_ref(v_b_1149_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5_spec__10(lean_object* v_00_u03b2_1151_, lean_object* v_m_1152_, lean_object* v_query_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5_spec__10___redArg(v_m_1152_, v_query_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5_spec__10___boxed(lean_object* v_00_u03b2_1155_, lean_object* v_m_1156_, lean_object* v_query_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5_spec__10(v_00_u03b2_1155_, v_m_1156_, v_query_1157_);
lean_dec(v_query_1157_);
lean_dec_ref(v_m_1156_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8_spec__9(lean_object* v_00_u03b2_1159_, lean_object* v_b_1160_, lean_object* v_acc_1161_, lean_object* v_i_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8_spec__9___redArg(v_b_1160_, v_acc_1161_, v_i_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8_spec__9___boxed(lean_object* v_00_u03b2_1164_, lean_object* v_b_1165_, lean_object* v_acc_1166_, lean_object* v_i_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4_spec__8_spec__9(v_00_u03b2_1164_, v_b_1165_, v_acc_1166_, v_i_1167_);
lean_dec_ref(v_b_1165_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___redArg(lean_object* v_f_1169_, lean_object* v_v_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
if (lean_obj_tag(v_v_1170_) == 0)
{
lean_object* v_code_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1200_; 
v_code_1176_ = lean_ctor_get(v_v_1170_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_v_1170_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1178_ = v_v_1170_;
v_isShared_1179_ = v_isSharedCheck_1200_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_code_1176_);
lean_dec(v_v_1170_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1200_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; 
lean_inc(v___y_1174_);
lean_inc_ref(v___y_1173_);
lean_inc(v___y_1172_);
lean_inc_ref(v___y_1171_);
v___x_1180_ = lean_apply_6(v_f_1169_, v_code_1176_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, lean_box(0));
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1191_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v_a_1181_);
v___x_1186_ = v___x_1178_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1188_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1186_);
v___x_1188_ = v___x_1183_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_del_object(v___x_1178_);
v_a_1192_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1180_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1180_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
else
{
lean_object* v___x_1201_; 
lean_dec_ref(v_f_1169_);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v_v_1170_);
return v___x_1201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___redArg___boxed(lean_object* v_f_1202_, lean_object* v_v_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___redArg(v_f_1202_, v_v_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0(uint8_t v_pu_1210_, lean_object* v_f_1211_, lean_object* v_v_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___redArg(v_f_1211_, v_v_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___boxed(lean_object* v_pu_1219_, lean_object* v_f_1220_, lean_object* v_v_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
uint8_t v_pu_boxed_1227_; lean_object* v_res_1228_; 
v_pu_boxed_1227_ = lean_unbox(v_pu_1219_);
v_res_1228_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0(v_pu_boxed_1227_, v_f_1220_, v_v_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC(lean_object* v_decl_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_toSignature_1236_; lean_object* v_value_1237_; uint8_t v_recursive_1238_; lean_object* v_inlineAttr_x3f_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1264_; 
v_toSignature_1236_ = lean_ctor_get(v_decl_1230_, 0);
v_value_1237_ = lean_ctor_get(v_decl_1230_, 1);
v_recursive_1238_ = lean_ctor_get_uint8(v_decl_1230_, sizeof(void*)*3);
v_inlineAttr_x3f_1239_ = lean_ctor_get(v_decl_1230_, 2);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_decl_1230_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1241_ = v_decl_1230_;
v_isShared_1242_ = v_isSharedCheck_1264_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_inlineAttr_x3f_1239_);
lean_inc(v_value_1237_);
lean_inc(v_toSignature_1236_);
lean_dec(v_decl_1230_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1264_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC___closed__0));
v___x_1244_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___redArg(v___x_1243_, v_value_1237_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1255_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1255_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1255_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v_a_1245_);
v___x_1250_ = v___x_1241_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_toSignature_1236_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_a_1245_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_inlineAttr_x3f_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, sizeof(void*)*3, v_recursive_1238_);
v___x_1250_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1252_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1250_);
v___x_1252_ = v___x_1247_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
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
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_del_object(v___x_1241_);
lean_dec(v_inlineAttr_x3f_1239_);
lean_dec_ref(v_toSignature_1236_);
v_a_1256_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1244_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1244_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC___boxed(lean_object* v_decl_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC(v_decl_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
return v_res_1271_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_coalesceRC___closed__3(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1276_ = lean_unsigned_to_nat(0u);
v___x_1277_ = ((lean_object*)(l_Lean_Compiler_LCNF_coalesceRC___closed__2));
v___x_1278_ = 2;
v___x_1279_ = ((lean_object*)(l_Lean_Compiler_LCNF_coalesceRC___closed__1));
v___x_1280_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1279_, v___x_1278_, v___x_1277_, v___x_1276_);
return v___x_1280_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_coalesceRC(void){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_obj_once(&l_Lean_Compiler_LCNF_coalesceRC___closed__3, &l_Lean_Compiler_LCNF_coalesceRC___closed__3_once, _init_l_Lean_Compiler_LCNF_coalesceRC___closed__3);
return v___x_1281_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = lean_unsigned_to_nat(3124848603u);
v___x_1338_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_));
v___x_1339_ = l_Lean_Name_num___override(v___x_1338_, v___x_1337_);
return v___x_1339_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_));
v___x_1342_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_);
v___x_1343_ = l_Lean_Name_str___override(v___x_1342_, v___x_1341_);
return v___x_1343_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_));
v___x_1346_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_);
v___x_1347_ = l_Lean_Name_str___override(v___x_1346_, v___x_1345_);
return v___x_1347_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = lean_unsigned_to_nat(2u);
v___x_1349_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_);
v___x_1350_ = l_Lean_Name_num___override(v___x_1349_, v___x_1348_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1352_; uint8_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1352_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_));
v___x_1353_ = 1;
v___x_1354_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_);
v___x_1355_ = l_Lean_registerTraceClass(v___x_1352_, v___x_1353_, v___x_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2____boxed(lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_();
return v_res_1357_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_CoalesceRC(uint8_t builtin) {
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
l_Lean_Compiler_LCNF_coalesceRC = _init_l_Lean_Compiler_LCNF_coalesceRC();
lean_mark_persistent(l_Lean_Compiler_LCNF_coalesceRC);
res = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_CoalesceRC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_CoalesceRC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_CoalesceRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_CoalesceRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_CoalesceRC(builtin);
}
#ifdef __cplusplus
}
#endif
