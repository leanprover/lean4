// Lean compiler output
// Module: Lean.Meta.Sym.SynthInstance
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.SynthInstance
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
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkInstLE;
extern lean_object* l_Lean_Int_mkType;
extern lean_object* l_Lean_Int_mkInstLT;
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkInstNeg;
extern lean_object* l_Lean_Int_mkInstPow;
extern lean_object* l_Lean_Int_mkInstPowNat;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkInstMod;
extern lean_object* l_Lean_Int_mkInstDiv;
extern lean_object* l_Lean_Int_mkInstMul;
extern lean_object* l_Lean_Int_mkInstSub;
extern lean_object* l_Lean_Int_mkInstAdd;
extern lean_object* l_Lean_Int_mkInstHPow;
extern lean_object* l_Lean_Int_mkInstHMod;
extern lean_object* l_Lean_Int_mkInstHDiv;
extern lean_object* l_Lean_Int_mkInstHMul;
extern lean_object* l_Lean_Int_mkInstHSub;
extern lean_object* l_Lean_Int_mkInstHAdd;
extern lean_object* l_Lean_Nat_mkInstLE;
extern lean_object* l_Lean_Nat_mkInstLT;
extern lean_object* l_Lean_Nat_mkInstNatPow;
extern lean_object* l_Lean_Nat_mkInstPow;
extern lean_object* l_Lean_Nat_mkInstMod;
extern lean_object* l_Lean_Nat_mkInstDiv;
extern lean_object* l_Lean_Nat_mkInstMul;
extern lean_object* l_Lean_Nat_mkInstSub;
extern lean_object* l_Lean_Nat_mkInstAdd;
extern lean_object* l_Lean_Nat_mkInstHPow;
extern lean_object* l_Lean_Nat_mkInstHMod;
extern lean_object* l_Lean_Nat_mkInstHDiv;
extern lean_object* l_Lean_Nat_mkInstHMul;
extern lean_object* l_Lean_Nat_mkInstHSub;
extern lean_object* l_Lean_Nat_mkInstHAdd;
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Meta_isDefEqStuckExceptionId;
lean_object* l_Lean_Meta_synthInstanceCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__3_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__7;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__8_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__11;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__12;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__13_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__17;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__18_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__19_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__22;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__23 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__23_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__24 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__24_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__26;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__27;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__28 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__28_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__29 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__29_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__31;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__32;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__33 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__33_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__34 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__34_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__38;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__39;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sub"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__40 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__40_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__40_value),LEAN_SCALAR_PTR_LITERAL(203, 50, 219, 228, 204, 142, 182, 246)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__41 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__41_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__43;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__44;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mul"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__45 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__45_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__45_value),LEAN_SCALAR_PTR_LITERAL(155, 25, 183, 66, 31, 85, 84, 65)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__46 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__46_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__48;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__49;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Div"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__50 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__50_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__50_value),LEAN_SCALAR_PTR_LITERAL(153, 247, 56, 19, 64, 245, 190, 87)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__51 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__51_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__53;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__54;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mod"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__55 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__55_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__55_value),LEAN_SCALAR_PTR_LITERAL(141, 157, 192, 123, 66, 123, 34, 2)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__56 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__56_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__58;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__59;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Pow"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__60 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__60_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__60_value),LEAN_SCALAR_PTR_LITERAL(237, 192, 51, 134, 187, 116, 61, 36)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__61 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__61_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__62;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__64;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__65;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "NatPow"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__66 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__66_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__66_value),LEAN_SCALAR_PTR_LITERAL(36, 252, 247, 75, 236, 16, 44, 32)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__67 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__67_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__69;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__70;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__71 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__71_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__71_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__72 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__72_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__74;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__75;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__76 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__76_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__76_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__77 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__77_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__79_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__79;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__80;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__81_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__81;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__82;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__83;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__84;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__85_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__85;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__86;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__87;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__88;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__89_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__89;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__90_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__90;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__91_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__91;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__92_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__92;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__93_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__93;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__94_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__94;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__95_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__95;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__96_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__96;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__97_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__97;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__98_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__98;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__99_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__99;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__100_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__100;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__101;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__102_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__102;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__103_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__103;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__104_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__104;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__105_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__105;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__106_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__106;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__107 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__107_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__107_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__108 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__108_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__109_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__109;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__110_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__110;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__111_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__111;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__112_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__112;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__113_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__113;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__114_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__114;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__115_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__115;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__116_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__116;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__117_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__117;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__118_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__118;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__119_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__119;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__120_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__120;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__121_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__121;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__122_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__122;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__123_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__123;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__124_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__124;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__125_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__125;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__126_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__126;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__127_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__127;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__128_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__128;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__129_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__129;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__130_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__130;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__131_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__131;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__132_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__132;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__133_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__133;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__134_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__134;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__135_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__135;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__136_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__136;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__137_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__137;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__138_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__138;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__139_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__139;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__140_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__140;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__141_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__141;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__142_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__142;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__143_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__143;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__144_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__144;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__145_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__145;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__146_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__146;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__147_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__147;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__148_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__148;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__149_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__149;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_synthInstanceMeta_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "sym typeclass inference"};
static const lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_synthInstanceMeta_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_synthInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "`sym` failed to find instance"};
static const lean_object* l_Lean_Meta_Sym_synthInstance___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_synthInstance___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_synthInstance___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_synthInstance___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
return v_x_1_;
}
else
{
lean_object* v_key_3_; lean_object* v_value_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_28_; 
v_key_3_ = lean_ctor_get(v_x_2_, 0);
v_value_4_ = lean_ctor_get(v_x_2_, 1);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v_isSharedCheck_28_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_28_ == 0)
{
v___x_7_ = v_x_2_;
v_isShared_8_ = v_isSharedCheck_28_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_value_4_);
lean_inc(v_key_3_);
lean_dec(v_x_2_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_28_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; uint64_t v___x_10_; uint64_t v___x_11_; uint64_t v___x_12_; uint64_t v_fold_13_; uint64_t v___x_14_; uint64_t v___x_15_; uint64_t v___x_16_; size_t v___x_17_; size_t v___x_18_; size_t v___x_19_; size_t v___x_20_; size_t v___x_21_; lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_9_ = lean_array_get_size(v_x_1_);
v___x_10_ = l_Lean_Expr_hash(v_key_3_);
v___x_11_ = 32ULL;
v___x_12_ = lean_uint64_shift_right(v___x_10_, v___x_11_);
v_fold_13_ = lean_uint64_xor(v___x_10_, v___x_12_);
v___x_14_ = 16ULL;
v___x_15_ = lean_uint64_shift_right(v_fold_13_, v___x_14_);
v___x_16_ = lean_uint64_xor(v_fold_13_, v___x_15_);
v___x_17_ = lean_uint64_to_usize(v___x_16_);
v___x_18_ = lean_usize_of_nat(v___x_9_);
v___x_19_ = ((size_t)1ULL);
v___x_20_ = lean_usize_sub(v___x_18_, v___x_19_);
v___x_21_ = lean_usize_land(v___x_17_, v___x_20_);
v___x_22_ = lean_array_uget_borrowed(v_x_1_, v___x_21_);
lean_inc(v___x_22_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 2, v___x_22_);
v___x_24_ = v___x_7_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_key_3_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_value_4_);
lean_ctor_set(v_reuseFailAlloc_27_, 2, v___x_22_);
v___x_24_ = v_reuseFailAlloc_27_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_25_; 
v___x_25_ = lean_array_uset(v_x_1_, v___x_21_, v___x_24_);
v_x_1_ = v___x_25_;
v_x_2_ = v_tail_5_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_29_, lean_object* v_source_30_, lean_object* v_target_31_){
_start:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_array_get_size(v_source_30_);
v___x_33_ = lean_nat_dec_lt(v_i_29_, v___x_32_);
if (v___x_33_ == 0)
{
lean_dec_ref(v_source_30_);
lean_dec(v_i_29_);
return v_target_31_;
}
else
{
lean_object* v_es_34_; lean_object* v___x_35_; lean_object* v_source_36_; lean_object* v_target_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_es_34_ = lean_array_fget(v_source_30_, v_i_29_);
v___x_35_ = lean_box(0);
v_source_36_ = lean_array_fset(v_source_30_, v_i_29_, v___x_35_);
v_target_37_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_31_, v_es_34_);
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_nat_add(v_i_29_, v___x_38_);
lean_dec(v_i_29_);
v_i_29_ = v___x_39_;
v_source_30_ = v_source_36_;
v_target_31_ = v_target_37_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2___redArg(lean_object* v_data_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_nbuckets_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_42_ = lean_array_get_size(v_data_41_);
v___x_43_ = lean_unsigned_to_nat(2u);
v_nbuckets_44_ = lean_nat_mul(v___x_42_, v___x_43_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_box(0);
v___x_47_ = lean_mk_array(v_nbuckets_44_, v___x_46_);
v___x_48_ = lean_array_propagate_mark(v_data_41_, v___x_47_);
v___x_49_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3___redArg(v___x_45_, v_data_41_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___redArg(lean_object* v_a_50_, lean_object* v_x_51_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
else
{
lean_object* v_key_53_; lean_object* v_tail_54_; uint8_t v___x_55_; 
v_key_53_ = lean_ctor_get(v_x_51_, 0);
v_tail_54_ = lean_ctor_get(v_x_51_, 2);
v___x_55_ = lean_expr_eqv(v_key_53_, v_a_50_);
if (v___x_55_ == 0)
{
v_x_51_ = v_tail_54_;
goto _start;
}
else
{
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_57_, lean_object* v_x_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___redArg(v_a_57_, v_x_58_);
lean_dec(v_x_58_);
lean_dec_ref(v_a_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__3___redArg(lean_object* v_a_61_, lean_object* v_b_62_, lean_object* v_x_63_){
_start:
{
if (lean_obj_tag(v_x_63_) == 0)
{
lean_dec(v_b_62_);
lean_dec_ref(v_a_61_);
return v_x_63_;
}
else
{
lean_object* v_key_64_; lean_object* v_value_65_; lean_object* v_tail_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_78_; 
v_key_64_ = lean_ctor_get(v_x_63_, 0);
v_value_65_ = lean_ctor_get(v_x_63_, 1);
v_tail_66_ = lean_ctor_get(v_x_63_, 2);
v_isSharedCheck_78_ = !lean_is_exclusive(v_x_63_);
if (v_isSharedCheck_78_ == 0)
{
v___x_68_ = v_x_63_;
v_isShared_69_ = v_isSharedCheck_78_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_tail_66_);
lean_inc(v_value_65_);
lean_inc(v_key_64_);
lean_dec(v_x_63_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_78_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
uint8_t v___x_70_; 
v___x_70_ = lean_expr_eqv(v_key_64_, v_a_61_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__3___redArg(v_a_61_, v_b_62_, v_tail_66_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 2, v___x_71_);
v___x_73_ = v___x_68_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_key_64_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_value_65_);
lean_ctor_set(v_reuseFailAlloc_74_, 2, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
else
{
lean_object* v___x_76_; 
lean_dec(v_value_65_);
lean_dec(v_key_64_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v_b_62_);
lean_ctor_set(v___x_68_, 0, v_a_61_);
v___x_76_ = v___x_68_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_61_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_b_62_);
lean_ctor_set(v_reuseFailAlloc_77_, 2, v_tail_66_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0___redArg(lean_object* v_m_79_, lean_object* v_a_80_, lean_object* v_b_81_){
_start:
{
lean_object* v_size_82_; lean_object* v_buckets_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_126_; 
v_size_82_ = lean_ctor_get(v_m_79_, 0);
v_buckets_83_ = lean_ctor_get(v_m_79_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_m_79_);
if (v_isSharedCheck_126_ == 0)
{
v___x_85_ = v_m_79_;
v_isShared_86_ = v_isSharedCheck_126_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_buckets_83_);
lean_inc(v_size_82_);
lean_dec(v_m_79_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_126_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; uint64_t v___x_88_; uint64_t v___x_89_; uint64_t v___x_90_; uint64_t v_fold_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v___x_94_; size_t v___x_95_; size_t v___x_96_; size_t v___x_97_; size_t v___x_98_; size_t v___x_99_; lean_object* v_bkt_100_; uint8_t v___x_101_; 
v___x_87_ = lean_array_get_size(v_buckets_83_);
v___x_88_ = l_Lean_Expr_hash(v_a_80_);
v___x_89_ = 32ULL;
v___x_90_ = lean_uint64_shift_right(v___x_88_, v___x_89_);
v_fold_91_ = lean_uint64_xor(v___x_88_, v___x_90_);
v___x_92_ = 16ULL;
v___x_93_ = lean_uint64_shift_right(v_fold_91_, v___x_92_);
v___x_94_ = lean_uint64_xor(v_fold_91_, v___x_93_);
v___x_95_ = lean_uint64_to_usize(v___x_94_);
v___x_96_ = lean_usize_of_nat(v___x_87_);
v___x_97_ = ((size_t)1ULL);
v___x_98_ = lean_usize_sub(v___x_96_, v___x_97_);
v___x_99_ = lean_usize_land(v___x_95_, v___x_98_);
v_bkt_100_ = lean_array_uget_borrowed(v_buckets_83_, v___x_99_);
v___x_101_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___redArg(v_a_80_, v_bkt_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v_size_x27_103_; lean_object* v___x_104_; lean_object* v_buckets_x27_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_102_ = lean_unsigned_to_nat(1u);
v_size_x27_103_ = lean_nat_add(v_size_82_, v___x_102_);
lean_dec(v_size_82_);
lean_inc(v_bkt_100_);
v___x_104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_104_, 0, v_a_80_);
lean_ctor_set(v___x_104_, 1, v_b_81_);
lean_ctor_set(v___x_104_, 2, v_bkt_100_);
v_buckets_x27_105_ = lean_array_uset(v_buckets_83_, v___x_99_, v___x_104_);
v___x_106_ = lean_unsigned_to_nat(4u);
v___x_107_ = lean_nat_mul(v_size_x27_103_, v___x_106_);
v___x_108_ = lean_unsigned_to_nat(3u);
v___x_109_ = lean_nat_div(v___x_107_, v___x_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_array_get_size(v_buckets_x27_105_);
v___x_111_ = lean_nat_dec_le(v___x_109_, v___x_110_);
lean_dec(v___x_109_);
if (v___x_111_ == 0)
{
lean_object* v_val_112_; lean_object* v___x_114_; 
v_val_112_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2___redArg(v_buckets_x27_105_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v_val_112_);
lean_ctor_set(v___x_85_, 0, v_size_x27_103_);
v___x_114_ = v___x_85_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_size_x27_103_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_val_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
else
{
lean_object* v___x_117_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v_buckets_x27_105_);
lean_ctor_set(v___x_85_, 0, v_size_x27_103_);
v___x_117_ = v___x_85_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_size_x27_103_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_buckets_x27_105_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
else
{
lean_object* v___x_119_; lean_object* v_buckets_x27_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
lean_inc(v_bkt_100_);
v___x_119_ = lean_box(0);
v_buckets_x27_120_ = lean_array_uset(v_buckets_83_, v___x_99_, v___x_119_);
v___x_121_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__3___redArg(v_a_80_, v_b_81_, v_bkt_100_);
v___x_122_ = lean_array_uset(v_buckets_x27_120_, v___x_99_, v___x_121_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v___x_122_);
v___x_124_ = v___x_85_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_size_82_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg(lean_object* v_as_x27_127_, lean_object* v_b_128_){
_start:
{
if (lean_obj_tag(v_as_x27_127_) == 0)
{
return v_b_128_;
}
else
{
lean_object* v_head_129_; lean_object* v_tail_130_; lean_object* v_fst_131_; lean_object* v_snd_132_; lean_object* v_r_133_; 
v_head_129_ = lean_ctor_get(v_as_x27_127_, 0);
v_tail_130_ = lean_ctor_get(v_as_x27_127_, 1);
v_fst_131_ = lean_ctor_get(v_head_129_, 0);
v_snd_132_ = lean_ctor_get(v_head_129_, 1);
lean_inc(v_snd_132_);
lean_inc(v_fst_131_);
v_r_133_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0___redArg(v_b_128_, v_fst_131_, v_snd_132_);
v_as_x27_127_ = v_tail_130_;
v_b_128_ = v_r_133_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_135_, lean_object* v_b_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg(v_as_x27_135_, v_b_136_);
lean_dec(v_as_x27_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0(lean_object* v_m_138_, lean_object* v_l_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg(v_l_139_, v_m_138_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0___boxed(lean_object* v_m_141_, lean_object* v_l_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0(v_m_141_, v_l_142_);
lean_dec(v_l_142_);
return v_res_143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5(void){
_start:
{
lean_object* v_us_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_us_156_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2));
v___x_157_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__4));
v___x_158_ = l_Lean_mkConst(v___x_157_, v_us_156_);
return v___x_158_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__6(void){
_start:
{
lean_object* v_nat_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_nat_159_ = l_Lean_Nat_mkType;
v___x_160_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5);
v___x_161_ = l_Lean_mkApp3(v___x_160_, v_nat_159_, v_nat_159_, v_nat_159_);
return v___x_161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__7(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = l_Lean_Nat_mkInstHAdd;
v___x_163_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__6, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__6_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__6);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
return v___x_164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10(void){
_start:
{
lean_object* v_us_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_us_168_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2));
v___x_169_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__9));
v___x_170_ = l_Lean_mkConst(v___x_169_, v_us_168_);
return v___x_170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__11(void){
_start:
{
lean_object* v_nat_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_nat_171_ = l_Lean_Nat_mkType;
v___x_172_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10);
v___x_173_ = l_Lean_mkApp3(v___x_172_, v_nat_171_, v_nat_171_, v_nat_171_);
return v___x_173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__12(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = l_Lean_Nat_mkInstHSub;
v___x_175_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__11, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__11_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__11);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15(void){
_start:
{
lean_object* v_us_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_us_180_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2));
v___x_181_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__14));
v___x_182_ = l_Lean_mkConst(v___x_181_, v_us_180_);
return v___x_182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__16(void){
_start:
{
lean_object* v_nat_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_nat_183_ = l_Lean_Nat_mkType;
v___x_184_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15);
v___x_185_ = l_Lean_mkApp3(v___x_184_, v_nat_183_, v_nat_183_, v_nat_183_);
return v___x_185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__17(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = l_Lean_Nat_mkInstHMul;
v___x_187_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__16, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__16_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__16);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20(void){
_start:
{
lean_object* v_us_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_us_192_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2));
v___x_193_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__19));
v___x_194_ = l_Lean_mkConst(v___x_193_, v_us_192_);
return v___x_194_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__21(void){
_start:
{
lean_object* v_nat_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_nat_195_ = l_Lean_Nat_mkType;
v___x_196_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20);
v___x_197_ = l_Lean_mkApp3(v___x_196_, v_nat_195_, v_nat_195_, v_nat_195_);
return v___x_197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__22(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = l_Lean_Nat_mkInstHDiv;
v___x_199_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__21, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__21_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__21);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25(void){
_start:
{
lean_object* v_us_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_us_204_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2));
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__24));
v___x_206_ = l_Lean_mkConst(v___x_205_, v_us_204_);
return v___x_206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__26(void){
_start:
{
lean_object* v_nat_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_nat_207_ = l_Lean_Nat_mkType;
v___x_208_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25);
v___x_209_ = l_Lean_mkApp3(v___x_208_, v_nat_207_, v_nat_207_, v_nat_207_);
return v___x_209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__27(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = l_Lean_Nat_mkInstHMod;
v___x_211_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__26, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__26_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__26);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
return v___x_212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30(void){
_start:
{
lean_object* v_us_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_us_216_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2));
v___x_217_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__29));
v___x_218_ = l_Lean_mkConst(v___x_217_, v_us_216_);
return v___x_218_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__31(void){
_start:
{
lean_object* v_nat_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_nat_219_ = l_Lean_Nat_mkType;
v___x_220_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30);
v___x_221_ = l_Lean_mkApp3(v___x_220_, v_nat_219_, v_nat_219_, v_nat_219_);
return v___x_221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__32(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = l_Lean_Nat_mkInstHPow;
v___x_223_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__31, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__31_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__31);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = l_Lean_Level_ofNat(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_box(0);
v___x_231_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35);
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36);
v___x_234_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__34));
v___x_235_ = l_Lean_mkConst(v___x_234_, v___x_233_);
return v___x_235_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__38(void){
_start:
{
lean_object* v_nat_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_nat_236_ = l_Lean_Nat_mkType;
v___x_237_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37);
v___x_238_ = l_Lean_Expr_app___override(v___x_237_, v_nat_236_);
return v___x_238_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__39(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = l_Lean_Nat_mkInstAdd;
v___x_240_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__38, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__38_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__38);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36);
v___x_246_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__41));
v___x_247_ = l_Lean_mkConst(v___x_246_, v___x_245_);
return v___x_247_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__43(void){
_start:
{
lean_object* v_nat_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_nat_248_ = l_Lean_Nat_mkType;
v___x_249_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42);
v___x_250_ = l_Lean_Expr_app___override(v___x_249_, v_nat_248_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__44(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = l_Lean_Nat_mkInstSub;
v___x_252_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__43, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__43_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__43);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36);
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__46));
v___x_259_ = l_Lean_mkConst(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__48(void){
_start:
{
lean_object* v_nat_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_nat_260_ = l_Lean_Nat_mkType;
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47);
v___x_262_ = l_Lean_Expr_app___override(v___x_261_, v_nat_260_);
return v___x_262_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__49(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = l_Lean_Nat_mkInstMul;
v___x_264_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__48, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__48_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__48);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36);
v___x_270_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__51));
v___x_271_ = l_Lean_mkConst(v___x_270_, v___x_269_);
return v___x_271_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__53(void){
_start:
{
lean_object* v_nat_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_nat_272_ = l_Lean_Nat_mkType;
v___x_273_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52);
v___x_274_ = l_Lean_Expr_app___override(v___x_273_, v_nat_272_);
return v___x_274_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__54(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = l_Lean_Nat_mkInstDiv;
v___x_276_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__53, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__53_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__53);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36);
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__56));
v___x_283_ = l_Lean_mkConst(v___x_282_, v___x_281_);
return v___x_283_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__58(void){
_start:
{
lean_object* v_nat_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_nat_284_ = l_Lean_Nat_mkType;
v___x_285_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57);
v___x_286_ = l_Lean_Expr_app___override(v___x_285_, v_nat_284_);
return v___x_286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__59(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = l_Lean_Nat_mkInstMod;
v___x_288_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__58, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__58_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__58);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__62(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36);
v___x_294_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35);
v___x_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__62, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__62_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__62);
v___x_297_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__61));
v___x_298_ = l_Lean_mkConst(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__64(void){
_start:
{
lean_object* v_nat_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_nat_299_ = l_Lean_Nat_mkType;
v___x_300_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63);
v___x_301_ = l_Lean_mkAppB(v___x_300_, v_nat_299_, v_nat_299_);
return v___x_301_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__65(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = l_Lean_Nat_mkInstPow;
v___x_303_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__64, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__64_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__64);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
return v___x_304_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36);
v___x_309_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__67));
v___x_310_ = l_Lean_mkConst(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__69(void){
_start:
{
lean_object* v_nat_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_nat_311_ = l_Lean_Nat_mkType;
v___x_312_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68);
v___x_313_ = l_Lean_Expr_app___override(v___x_312_, v_nat_311_);
return v___x_313_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__70(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = l_Lean_Nat_mkInstNatPow;
v___x_315_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__69, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__69_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__69);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36);
v___x_321_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__72));
v___x_322_ = l_Lean_mkConst(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__74(void){
_start:
{
lean_object* v_nat_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_nat_323_ = l_Lean_Nat_mkType;
v___x_324_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73);
v___x_325_ = l_Lean_Expr_app___override(v___x_324_, v_nat_323_);
return v___x_325_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__75(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = l_Lean_Nat_mkInstLT;
v___x_327_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__74, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__74_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__74);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
return v___x_328_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36);
v___x_333_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__77));
v___x_334_ = l_Lean_mkConst(v___x_333_, v___x_332_);
return v___x_334_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__79(void){
_start:
{
lean_object* v_nat_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_nat_335_ = l_Lean_Nat_mkType;
v___x_336_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78);
v___x_337_ = l_Lean_Expr_app___override(v___x_336_, v_nat_335_);
return v___x_337_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__80(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = l_Lean_Nat_mkInstLE;
v___x_339_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__79, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__79_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__79);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_338_);
return v___x_340_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__81(void){
_start:
{
lean_object* v_int_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_int_341_ = l_Lean_Int_mkType;
v___x_342_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5);
v___x_343_ = l_Lean_mkApp3(v___x_342_, v_int_341_, v_int_341_, v_int_341_);
return v___x_343_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__82(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = l_Lean_Int_mkInstHAdd;
v___x_345_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__81, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__81_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__81);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__83(void){
_start:
{
lean_object* v_int_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_int_347_ = l_Lean_Int_mkType;
v___x_348_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10);
v___x_349_ = l_Lean_mkApp3(v___x_348_, v_int_347_, v_int_347_, v_int_347_);
return v___x_349_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__84(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = l_Lean_Int_mkInstHSub;
v___x_351_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__83, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__83_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__83);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_350_);
return v___x_352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__85(void){
_start:
{
lean_object* v_int_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_int_353_ = l_Lean_Int_mkType;
v___x_354_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15);
v___x_355_ = l_Lean_mkApp3(v___x_354_, v_int_353_, v_int_353_, v_int_353_);
return v___x_355_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__86(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = l_Lean_Int_mkInstHMul;
v___x_357_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__85, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__85_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__85);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__87(void){
_start:
{
lean_object* v_int_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_int_359_ = l_Lean_Int_mkType;
v___x_360_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20);
v___x_361_ = l_Lean_mkApp3(v___x_360_, v_int_359_, v_int_359_, v_int_359_);
return v___x_361_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__88(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = l_Lean_Int_mkInstHDiv;
v___x_363_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__87, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__87_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__87);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___x_362_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__89(void){
_start:
{
lean_object* v_int_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_int_365_ = l_Lean_Int_mkType;
v___x_366_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25);
v___x_367_ = l_Lean_mkApp3(v___x_366_, v_int_365_, v_int_365_, v_int_365_);
return v___x_367_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__90(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = l_Lean_Int_mkInstHMod;
v___x_369_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__89, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__89_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__89);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___x_368_);
return v___x_370_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__91(void){
_start:
{
lean_object* v_nat_371_; lean_object* v_int_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_nat_371_ = l_Lean_Nat_mkType;
v_int_372_ = l_Lean_Int_mkType;
v___x_373_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30);
v___x_374_ = l_Lean_mkApp3(v___x_373_, v_int_372_, v_nat_371_, v_int_372_);
return v___x_374_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__92(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = l_Lean_Int_mkInstHPow;
v___x_376_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__91, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__91_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__91);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__93(void){
_start:
{
lean_object* v_int_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_int_378_ = l_Lean_Int_mkType;
v___x_379_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37);
v___x_380_ = l_Lean_Expr_app___override(v___x_379_, v_int_378_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__94(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = l_Lean_Int_mkInstAdd;
v___x_382_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__93, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__93_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__93);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
return v___x_383_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__95(void){
_start:
{
lean_object* v_int_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_int_384_ = l_Lean_Int_mkType;
v___x_385_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42);
v___x_386_ = l_Lean_Expr_app___override(v___x_385_, v_int_384_);
return v___x_386_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__96(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = l_Lean_Int_mkInstSub;
v___x_388_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__95, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__95_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__95);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_387_);
return v___x_389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__97(void){
_start:
{
lean_object* v_int_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_int_390_ = l_Lean_Int_mkType;
v___x_391_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47);
v___x_392_ = l_Lean_Expr_app___override(v___x_391_, v_int_390_);
return v___x_392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__98(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = l_Lean_Int_mkInstMul;
v___x_394_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__97, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__97_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__97);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_393_);
return v___x_395_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__99(void){
_start:
{
lean_object* v_int_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_int_396_ = l_Lean_Int_mkType;
v___x_397_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52);
v___x_398_ = l_Lean_Expr_app___override(v___x_397_, v_int_396_);
return v___x_398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__100(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = l_Lean_Int_mkInstDiv;
v___x_400_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__99, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__99_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__99);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__101(void){
_start:
{
lean_object* v_int_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_int_402_ = l_Lean_Int_mkType;
v___x_403_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57);
v___x_404_ = l_Lean_Expr_app___override(v___x_403_, v_int_402_);
return v___x_404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__102(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = l_Lean_Int_mkInstMod;
v___x_406_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__101, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__101_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__101);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__103(void){
_start:
{
lean_object* v_nat_408_; lean_object* v_int_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_nat_408_ = l_Lean_Nat_mkType;
v_int_409_ = l_Lean_Int_mkType;
v___x_410_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63);
v___x_411_ = l_Lean_mkAppB(v___x_410_, v_int_409_, v_nat_408_);
return v___x_411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__104(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = l_Lean_Int_mkInstPowNat;
v___x_413_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__103, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__103_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__103);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_412_);
return v___x_414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__105(void){
_start:
{
lean_object* v_int_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_int_415_ = l_Lean_Int_mkType;
v___x_416_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68);
v___x_417_ = l_Lean_Expr_app___override(v___x_416_, v_int_415_);
return v___x_417_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__106(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = l_Lean_Int_mkInstPow;
v___x_419_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__105, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__105_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__105);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_418_);
return v___x_420_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__109(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36);
v___x_425_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__108));
v___x_426_ = l_Lean_mkConst(v___x_425_, v___x_424_);
return v___x_426_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__110(void){
_start:
{
lean_object* v_int_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_int_427_ = l_Lean_Int_mkType;
v___x_428_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__109, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__109_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__109);
v___x_429_ = l_Lean_Expr_app___override(v___x_428_, v_int_427_);
return v___x_429_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__111(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = l_Lean_Int_mkInstNeg;
v___x_431_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__110, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__110_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__110);
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
return v___x_432_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__112(void){
_start:
{
lean_object* v_int_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_int_433_ = l_Lean_Int_mkType;
v___x_434_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73);
v___x_435_ = l_Lean_Expr_app___override(v___x_434_, v_int_433_);
return v___x_435_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__113(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = l_Lean_Int_mkInstLT;
v___x_437_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__112, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__112_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__112);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_436_);
return v___x_438_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__114(void){
_start:
{
lean_object* v_int_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_int_439_ = l_Lean_Int_mkType;
v___x_440_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78);
v___x_441_ = l_Lean_Expr_app___override(v___x_440_, v_int_439_);
return v___x_441_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__115(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = l_Lean_Int_mkInstLE;
v___x_443_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__114, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__114_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__114);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
return v___x_444_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__116(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_box(0);
v___x_446_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__115, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__115_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__115);
v___x_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
return v___x_447_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__117(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_448_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__116, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__116_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__116);
v___x_449_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__113, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__113_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__113);
v___x_450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v___x_448_);
return v___x_450_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__118(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__117, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__117_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__117);
v___x_452_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__111, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__111_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__111);
v___x_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__119(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__118, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__118_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__118);
v___x_455_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__106, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__106_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__106);
v___x_456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__120(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__119, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__119_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__119);
v___x_458_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__104, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__104_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__104);
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__121(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__120, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__120_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__120);
v___x_461_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__102, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__102_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__102);
v___x_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
return v___x_462_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__122(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__121, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__121_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__121);
v___x_464_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__100, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__100_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__100);
v___x_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_463_);
return v___x_465_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__123(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__122, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__122_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__122);
v___x_467_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__98, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__98_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__98);
v___x_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__124(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__123, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__123_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__123);
v___x_470_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__96, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__96_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__96);
v___x_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__125(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__124, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__124_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__124);
v___x_473_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__94, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__94_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__94);
v___x_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_472_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__126(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__125, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__125_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__125);
v___x_476_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__92, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__92_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__92);
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__127(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__126, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__126_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__126);
v___x_479_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__90, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__90_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__90);
v___x_480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__128(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__127, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__127_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__127);
v___x_482_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__88, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__88_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__88);
v___x_483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__129(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__128, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__128_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__128);
v___x_485_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__86, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__86_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__86);
v___x_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
return v___x_486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__130(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__129, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__129_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__129);
v___x_488_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__84, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__84_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__84);
v___x_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
return v___x_489_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__131(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__130, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__130_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__130);
v___x_491_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__82, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__82_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__82);
v___x_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_490_);
return v___x_492_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__132(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__131, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__131_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__131);
v___x_494_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__80, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__80_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__80);
v___x_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_493_);
return v___x_495_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__133(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__132, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__132_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__132);
v___x_497_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__75, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__75_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__75);
v___x_498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v___x_496_);
return v___x_498_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__134(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__133, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__133_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__133);
v___x_500_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__70, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__70_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__70);
v___x_501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v___x_499_);
return v___x_501_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__135(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__134, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__134_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__134);
v___x_503_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__65, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__65_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__65);
v___x_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v___x_502_);
return v___x_504_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__136(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__135, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__135_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__135);
v___x_506_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__59, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__59_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__59);
v___x_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
return v___x_507_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__137(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__136, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__136_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__136);
v___x_509_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__54, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__54_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__54);
v___x_510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v___x_508_);
return v___x_510_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__138(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__137, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__137_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__137);
v___x_512_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__49, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__49_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__49);
v___x_513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v___x_511_);
return v___x_513_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__139(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__138, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__138_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__138);
v___x_515_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__44, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__44_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__44);
v___x_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v___x_514_);
return v___x_516_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__140(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__139, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__139_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__139);
v___x_518_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__39, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__39_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__39);
v___x_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v___x_517_);
return v___x_519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__141(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__140, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__140_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__140);
v___x_521_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__32, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__32_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__32);
v___x_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___x_520_);
return v___x_522_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__142(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__141, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__141_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__141);
v___x_524_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__27, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__27_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__27);
v___x_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__143(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__142, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__142_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__142);
v___x_527_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__22, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__22_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__22);
v___x_528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___x_526_);
return v___x_528_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__144(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__143, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__143_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__143);
v___x_530_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__17, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__17_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__17);
v___x_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__145(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__144, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__144_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__144);
v___x_533_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__12, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__12_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__12);
v___x_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
return v___x_534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__146(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__145, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__145_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__145);
v___x_536_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__7, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__7_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__7);
v___x_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
return v___x_537_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__147(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_box(0);
v___x_539_ = lean_unsigned_to_nat(16u);
v___x_540_ = lean_mk_array(v___x_539_, v___x_538_);
return v___x_540_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__148(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__147, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__147_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__147);
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v___x_541_);
return v___x_543_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__149(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__148, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__148_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__148);
v___x_545_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__146, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__146_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__146);
v___x_546_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg(v___x_545_, v___x_544_);
return v___x_546_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts(void){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__149, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__149_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__149);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0(lean_object* v_00_u03b2_548_, lean_object* v_m_549_, lean_object* v_a_550_, lean_object* v_b_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0___redArg(v_m_549_, v_a_550_, v_b_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1(lean_object* v_as_553_, lean_object* v_as_x27_554_, lean_object* v_b_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg(v_as_x27_554_, v_b_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___boxed(lean_object* v_as_558_, lean_object* v_as_x27_559_, lean_object* v_b_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1(v_as_558_, v_as_x27_559_, v_b_560_, v_a_561_);
lean_dec(v_as_x27_559_);
lean_dec(v_as_558_);
return v_res_562_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_563_, lean_object* v_a_564_, lean_object* v_x_565_){
_start:
{
uint8_t v___x_566_; 
v___x_566_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___redArg(v_a_564_, v_x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_567_, lean_object* v_a_568_, lean_object* v_x_569_){
_start:
{
uint8_t v_res_570_; lean_object* v_r_571_; 
v_res_570_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1(v_00_u03b2_567_, v_a_568_, v_x_569_);
lean_dec(v_x_569_);
lean_dec_ref(v_a_568_);
v_r_571_ = lean_box(v_res_570_);
return v_r_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_572_, lean_object* v_data_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2___redArg(v_data_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_575_, lean_object* v_a_576_, lean_object* v_b_577_, lean_object* v_x_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__3___redArg(v_a_576_, v_b_577_, v_x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_580_, lean_object* v_i_581_, lean_object* v_source_582_, lean_object* v_target_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3___redArg(v_i_581_, v_source_582_, v_target_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_585_, lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_586_, v_x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(lean_object* v_a_589_, lean_object* v_x_590_){
_start:
{
if (lean_obj_tag(v_x_590_) == 0)
{
lean_object* v___x_591_; 
v___x_591_ = lean_box(0);
return v___x_591_;
}
else
{
lean_object* v_key_592_; lean_object* v_value_593_; lean_object* v_tail_594_; uint8_t v___x_595_; 
v_key_592_ = lean_ctor_get(v_x_590_, 0);
v_value_593_ = lean_ctor_get(v_x_590_, 1);
v_tail_594_ = lean_ctor_get(v_x_590_, 2);
v___x_595_ = lean_expr_eqv(v_key_592_, v_a_589_);
if (v___x_595_ == 0)
{
v_x_590_ = v_tail_594_;
goto _start;
}
else
{
lean_object* v___x_597_; 
lean_inc(v_value_593_);
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_value_593_);
return v___x_597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_598_, lean_object* v_x_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(v_a_598_, v_x_599_);
lean_dec(v_x_599_);
lean_dec_ref(v_a_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(lean_object* v_m_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_buckets_603_; lean_object* v___x_604_; uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v___x_607_; uint64_t v_fold_608_; uint64_t v___x_609_; uint64_t v___x_610_; uint64_t v___x_611_; size_t v___x_612_; size_t v___x_613_; size_t v___x_614_; size_t v___x_615_; size_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_buckets_603_ = lean_ctor_get(v_m_601_, 1);
v___x_604_ = lean_array_get_size(v_buckets_603_);
v___x_605_ = l_Lean_Expr_hash(v_a_602_);
v___x_606_ = 32ULL;
v___x_607_ = lean_uint64_shift_right(v___x_605_, v___x_606_);
v_fold_608_ = lean_uint64_xor(v___x_605_, v___x_607_);
v___x_609_ = 16ULL;
v___x_610_ = lean_uint64_shift_right(v_fold_608_, v___x_609_);
v___x_611_ = lean_uint64_xor(v_fold_608_, v___x_610_);
v___x_612_ = lean_uint64_to_usize(v___x_611_);
v___x_613_ = lean_usize_of_nat(v___x_604_);
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_sub(v___x_613_, v___x_614_);
v___x_616_ = lean_usize_land(v___x_612_, v___x_615_);
v___x_617_ = lean_array_uget_borrowed(v_buckets_603_, v___x_616_);
v___x_618_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(v_a_602_, v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg___boxed(lean_object* v_m_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v_m_619_, v_a_620_);
lean_dec_ref(v_a_620_);
lean_dec_ref(v_m_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f(lean_object* v_type_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts;
v___x_624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v___x_623_, v_type_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___boxed(lean_object* v_type_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Meta_Sym_getBuiltinInstance_x3f(v_type_625_);
lean_dec_ref(v_type_625_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0(lean_object* v_00_u03b2_627_, lean_object* v_m_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v_m_628_, v_a_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___boxed(lean_object* v_00_u03b2_631_, lean_object* v_m_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0(v_00_u03b2_631_, v_m_632_, v_a_633_);
lean_dec_ref(v_a_633_);
lean_dec_ref(v_m_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0(lean_object* v_00_u03b2_635_, lean_object* v_a_636_, lean_object* v_x_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(v_a_636_, v_x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_639_, lean_object* v_a_640_, lean_object* v_x_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0(v_00_u03b2_639_, v_a_640_, v_x_641_);
lean_dec(v_x_641_);
lean_dec_ref(v_a_640_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(lean_object* v_category_643_, lean_object* v_opts_644_, lean_object* v_act_645_, lean_object* v_decl_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_inc(v___y_650_);
lean_inc_ref(v___y_649_);
lean_inc(v___y_648_);
lean_inc_ref(v___y_647_);
v___x_652_ = lean_apply_4(v_act_645_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
v___x_653_ = l_Lean_profileitIOUnsafe___redArg(v_category_643_, v_opts_644_, v___x_652_, v_decl_646_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg___boxed(lean_object* v_category_654_, lean_object* v_opts_655_, lean_object* v_act_656_, lean_object* v_decl_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v_category_654_, v_opts_655_, v_act_656_, v_decl_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v_opts_655_);
lean_dec_ref(v_category_654_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(lean_object* v_00_u03b1_664_, lean_object* v_category_665_, lean_object* v_opts_666_, lean_object* v_act_667_, lean_object* v_decl_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v_category_665_, v_opts_666_, v_act_667_, v_decl_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___boxed(lean_object* v_00_u03b1_675_, lean_object* v_category_676_, lean_object* v_opts_677_, lean_object* v_act_678_, lean_object* v_decl_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(v_00_u03b1_675_, v_category_676_, v_opts_677_, v_act_678_, v_decl_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec_ref(v_opts_677_);
lean_dec_ref(v_category_676_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(lean_object* v___x_686_, lean_object* v_type_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
if (lean_obj_tag(v___x_686_) == 1)
{
lean_object* v___x_693_; 
lean_dec_ref(v_type_687_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_686_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec(v___x_686_);
v___x_694_ = l_Lean_Meta_isDefEqStuckExceptionId;
v___x_695_ = lean_box(0);
v___x_696_ = l_Lean_Meta_synthInstanceCore_x3f(v_type_687_, v___x_695_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_696_) == 0)
{
return v___x_696_;
}
else
{
lean_object* v_a_697_; uint8_t v___x_698_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v___x_698_ = l_Lean_Exception_isInterrupt(v_a_697_);
if (v___x_698_ == 0)
{
uint8_t v___x_699_; 
lean_inc(v_a_697_);
v___x_699_ = l_Lean_Exception_isRuntime(v_a_697_);
if (v___x_699_ == 0)
{
if (lean_obj_tag(v_a_697_) == 0)
{
return v___x_696_;
}
else
{
lean_object* v_id_700_; uint8_t v___x_701_; 
v_id_700_ = lean_ctor_get(v_a_697_, 0);
v___x_701_ = l_Lean_instBEqInternalExceptionId_beq(v___x_694_, v_id_700_);
if (v___x_701_ == 0)
{
return v___x_696_;
}
else
{
lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v___x_696_, 0);
lean_dec(v_unused_709_);
v___x_703_ = v___x_696_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_dec(v___x_696_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 0);
lean_ctor_set(v___x_703_, 0, v___x_695_);
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_695_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
else
{
return v___x_696_;
}
}
else
{
return v___x_696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed(lean_object* v___x_710_, lean_object* v_type_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(v___x_710_, v_type_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object* v_type_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___y_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_725_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_722_);
v___x_726_ = ((lean_object*)(l_Lean_Meta_Sym_synthInstanceMeta_x3f___closed__0));
v___x_727_ = l_Lean_Meta_Sym_getBuiltinInstance_x3f(v_type_719_);
lean_inc_ref(v_type_719_);
v___y_728_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___y_728_, 0, v___x_727_);
lean_closure_set(v___y_728_, 1, v_type_719_);
v___x_729_ = l_Lean_Expr_getAppFn(v_type_719_);
lean_dec_ref(v_type_719_);
v___x_730_ = l_Lean_Expr_constName_x3f(v___x_729_);
lean_dec_ref(v___x_729_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_box(0);
v___x_732_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v___x_726_, v___x_725_, v___y_728_, v___x_731_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
lean_dec_ref(v___x_725_);
return v___x_732_;
}
else
{
lean_object* v_val_733_; lean_object* v___x_734_; 
v_val_733_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_val_733_);
lean_dec_ref_known(v___x_730_, 1);
v___x_734_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v___x_726_, v___x_725_, v___y_728_, v_val_733_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
lean_dec_ref(v___x_725_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___boxed(lean_object* v_type_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
lean_object* v_ks_746_; lean_object* v_vs_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_771_; 
v_ks_746_ = lean_ctor_get(v_x_742_, 0);
v_vs_747_ = lean_ctor_get(v_x_742_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_x_742_);
if (v_isSharedCheck_771_ == 0)
{
v___x_749_ = v_x_742_;
v_isShared_750_ = v_isSharedCheck_771_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_vs_747_);
lean_inc(v_ks_746_);
lean_dec(v_x_742_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_771_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_array_get_size(v_ks_746_);
v___x_752_ = lean_nat_dec_lt(v_x_743_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
lean_dec(v_x_743_);
v___x_753_ = lean_array_push(v_ks_746_, v_x_744_);
v___x_754_ = lean_array_push(v_vs_747_, v_x_745_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_754_);
lean_ctor_set(v___x_749_, 0, v___x_753_);
v___x_756_ = v___x_749_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
else
{
lean_object* v_k_x27_758_; uint8_t v___x_759_; 
v_k_x27_758_ = lean_array_fget_borrowed(v_ks_746_, v_x_743_);
v___x_759_ = lean_expr_eqv(v_x_744_, v_k_x27_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_761_; 
if (v_isShared_750_ == 0)
{
v___x_761_ = v___x_749_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_ks_746_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_vs_747_);
v___x_761_ = v_reuseFailAlloc_765_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v_x_743_, v___x_762_);
lean_dec(v_x_743_);
v_x_742_ = v___x_761_;
v_x_743_ = v___x_763_;
goto _start;
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_766_ = lean_array_fset(v_ks_746_, v_x_743_, v_x_744_);
v___x_767_ = lean_array_fset(v_vs_747_, v_x_743_, v_x_745_);
lean_dec(v_x_743_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_767_);
lean_ctor_set(v___x_749_, 0, v___x_766_);
v___x_769_ = v___x_749_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_n_772_, lean_object* v_k_773_, lean_object* v_v_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_772_, v___x_775_, v_k_773_, v_v_774_);
return v___x_776_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(lean_object* v_x_778_, size_t v_x_779_, size_t v_x_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
lean_object* v_es_783_; size_t v___x_784_; size_t v___x_785_; lean_object* v_j_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_es_783_ = lean_ctor_get(v_x_778_, 0);
v___x_784_ = ((size_t)31ULL);
v___x_785_ = lean_usize_land(v_x_779_, v___x_784_);
v_j_786_ = lean_usize_to_nat(v___x_785_);
v___x_787_ = lean_array_get_size(v_es_783_);
v___x_788_ = lean_nat_dec_lt(v_j_786_, v___x_787_);
if (v___x_788_ == 0)
{
lean_dec(v_j_786_);
lean_dec(v_x_782_);
lean_dec_ref(v_x_781_);
return v_x_778_;
}
else
{
lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_827_; 
lean_inc_ref(v_es_783_);
v_isSharedCheck_827_ = !lean_is_exclusive(v_x_778_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v_x_778_, 0);
lean_dec(v_unused_828_);
v___x_790_ = v_x_778_;
v_isShared_791_ = v_isSharedCheck_827_;
goto v_resetjp_789_;
}
else
{
lean_dec(v_x_778_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_827_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_v_792_; lean_object* v___x_793_; lean_object* v_xs_x27_794_; lean_object* v___y_796_; 
v_v_792_ = lean_array_fget(v_es_783_, v_j_786_);
v___x_793_ = lean_box(0);
v_xs_x27_794_ = lean_array_fset(v_es_783_, v_j_786_, v___x_793_);
switch(lean_obj_tag(v_v_792_))
{
case 0:
{
lean_object* v_key_801_; lean_object* v_val_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_812_; 
v_key_801_ = lean_ctor_get(v_v_792_, 0);
v_val_802_ = lean_ctor_get(v_v_792_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v_v_792_);
if (v_isSharedCheck_812_ == 0)
{
v___x_804_ = v_v_792_;
v_isShared_805_ = v_isSharedCheck_812_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_val_802_);
lean_inc(v_key_801_);
lean_dec(v_v_792_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_812_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
uint8_t v___x_806_; 
v___x_806_ = lean_expr_eqv(v_x_781_, v_key_801_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_del_object(v___x_804_);
v___x_807_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_801_, v_val_802_, v_x_781_, v_x_782_);
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
v___y_796_ = v___x_808_;
goto v___jp_795_;
}
else
{
lean_object* v___x_810_; 
lean_dec(v_val_802_);
lean_dec(v_key_801_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v_x_782_);
lean_ctor_set(v___x_804_, 0, v_x_781_);
v___x_810_ = v___x_804_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_x_781_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_x_782_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
v___y_796_ = v___x_810_;
goto v___jp_795_;
}
}
}
}
case 1:
{
lean_object* v_node_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_825_; 
v_node_813_ = lean_ctor_get(v_v_792_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v_v_792_);
if (v_isSharedCheck_825_ == 0)
{
v___x_815_ = v_v_792_;
v_isShared_816_ = v_isSharedCheck_825_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_node_813_);
lean_dec(v_v_792_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_825_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
size_t v___x_817_; size_t v___x_818_; size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_817_ = ((size_t)5ULL);
v___x_818_ = lean_usize_shift_right(v_x_779_, v___x_817_);
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_add(v_x_780_, v___x_819_);
v___x_821_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_node_813_, v___x_818_, v___x_820_, v_x_781_, v_x_782_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_821_);
v___x_823_ = v___x_815_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
v___y_796_ = v___x_823_;
goto v___jp_795_;
}
}
}
default: 
{
lean_object* v___x_826_; 
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v_x_781_);
lean_ctor_set(v___x_826_, 1, v_x_782_);
v___y_796_ = v___x_826_;
goto v___jp_795_;
}
}
v___jp_795_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_array_fset(v_xs_x27_794_, v_j_786_, v___y_796_);
lean_dec(v_j_786_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_797_);
v___x_799_ = v___x_790_;
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
}
}
else
{
lean_object* v_ks_829_; lean_object* v_vs_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_848_; 
v_ks_829_ = lean_ctor_get(v_x_778_, 0);
v_vs_830_ = lean_ctor_get(v_x_778_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_x_778_);
if (v_isSharedCheck_848_ == 0)
{
v___x_832_ = v_x_778_;
v_isShared_833_ = v_isSharedCheck_848_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_vs_830_);
lean_inc(v_ks_829_);
lean_dec(v_x_778_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_848_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_ks_829_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_vs_830_);
v___x_835_ = v_reuseFailAlloc_847_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v_newNode_836_; size_t v___x_837_; uint8_t v___x_838_; 
v_newNode_836_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(v___x_835_, v_x_781_, v_x_782_);
v___x_837_ = ((size_t)7ULL);
v___x_838_ = lean_usize_dec_le(v___x_837_, v_x_780_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_839_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_836_);
v___x_840_ = lean_unsigned_to_nat(4u);
v___x_841_ = lean_nat_dec_lt(v___x_839_, v___x_840_);
lean_dec(v___x_839_);
if (v___x_841_ == 0)
{
lean_object* v_ks_842_; lean_object* v_vs_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_ks_842_ = lean_ctor_get(v_newNode_836_, 0);
lean_inc_ref(v_ks_842_);
v_vs_843_ = lean_ctor_get(v_newNode_836_, 1);
lean_inc_ref(v_vs_843_);
lean_dec_ref(v_newNode_836_);
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0);
v___x_846_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_x_780_, v_ks_842_, v_vs_843_, v___x_844_, v___x_845_);
lean_dec_ref(v_vs_843_);
lean_dec_ref(v_ks_842_);
return v___x_846_;
}
else
{
return v_newNode_836_;
}
}
else
{
return v_newNode_836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(size_t v_depth_849_, lean_object* v_keys_850_, lean_object* v_vals_851_, lean_object* v_i_852_, lean_object* v_entries_853_){
_start:
{
lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_854_ = lean_array_get_size(v_keys_850_);
v___x_855_ = lean_nat_dec_lt(v_i_852_, v___x_854_);
if (v___x_855_ == 0)
{
lean_dec(v_i_852_);
return v_entries_853_;
}
else
{
lean_object* v_k_856_; lean_object* v_v_857_; uint64_t v___x_858_; size_t v_h_859_; size_t v___x_860_; lean_object* v___x_861_; size_t v___x_862_; size_t v___x_863_; size_t v___x_864_; size_t v_h_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_k_856_ = lean_array_fget_borrowed(v_keys_850_, v_i_852_);
v_v_857_ = lean_array_fget_borrowed(v_vals_851_, v_i_852_);
v___x_858_ = l_Lean_Expr_hash(v_k_856_);
v_h_859_ = lean_uint64_to_usize(v___x_858_);
v___x_860_ = ((size_t)5ULL);
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_sub(v_depth_849_, v___x_862_);
v___x_864_ = lean_usize_mul(v___x_860_, v___x_863_);
v_h_865_ = lean_usize_shift_right(v_h_859_, v___x_864_);
v___x_866_ = lean_nat_add(v_i_852_, v___x_861_);
lean_dec(v_i_852_);
lean_inc(v_v_857_);
lean_inc(v_k_856_);
v___x_867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_entries_853_, v_h_865_, v_depth_849_, v_k_856_, v_v_857_);
v_i_852_ = v___x_866_;
v_entries_853_ = v___x_867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_869_, lean_object* v_keys_870_, lean_object* v_vals_871_, lean_object* v_i_872_, lean_object* v_entries_873_){
_start:
{
size_t v_depth_boxed_874_; lean_object* v_res_875_; 
v_depth_boxed_874_ = lean_unbox_usize(v_depth_869_);
lean_dec(v_depth_869_);
v_res_875_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_depth_boxed_874_, v_keys_870_, v_vals_871_, v_i_872_, v_entries_873_);
lean_dec_ref(v_vals_871_);
lean_dec_ref(v_keys_870_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___boxed(lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
size_t v_x_737__boxed_881_; size_t v_x_738__boxed_882_; lean_object* v_res_883_; 
v_x_737__boxed_881_ = lean_unbox_usize(v_x_877_);
lean_dec(v_x_877_);
v_x_738__boxed_882_ = lean_unbox_usize(v_x_878_);
lean_dec(v_x_878_);
v_res_883_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_876_, v_x_737__boxed_881_, v_x_738__boxed_882_, v_x_879_, v_x_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(lean_object* v_x_884_, lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
uint64_t v___x_887_; size_t v___x_888_; size_t v___x_889_; lean_object* v___x_890_; 
v___x_887_ = l_Lean_Expr_hash(v_x_885_);
v___x_888_ = lean_uint64_to_usize(v___x_887_);
v___x_889_ = ((size_t)1ULL);
v___x_890_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_884_, v___x_888_, v___x_889_, v_x_885_, v_x_886_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object* v_type_891_, lean_object* v_inst_892_, lean_object* v_a_893_){
_start:
{
lean_object* v___x_895_; lean_object* v_share_896_; lean_object* v_maxFVar_897_; lean_object* v_proofInstInfo_898_; lean_object* v_proofInstInfoFVar_899_; lean_object* v_inferType_900_; lean_object* v_getLevel_901_; lean_object* v_congrInfo_902_; lean_object* v_defEqI_903_; lean_object* v_extensions_904_; lean_object* v_issues_905_; lean_object* v_canon_906_; lean_object* v_instanceOverrides_907_; uint8_t v_debug_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_919_; 
v___x_895_ = lean_st_ref_take(v_a_893_);
v_share_896_ = lean_ctor_get(v___x_895_, 0);
v_maxFVar_897_ = lean_ctor_get(v___x_895_, 1);
v_proofInstInfo_898_ = lean_ctor_get(v___x_895_, 2);
v_proofInstInfoFVar_899_ = lean_ctor_get(v___x_895_, 3);
v_inferType_900_ = lean_ctor_get(v___x_895_, 4);
v_getLevel_901_ = lean_ctor_get(v___x_895_, 5);
v_congrInfo_902_ = lean_ctor_get(v___x_895_, 6);
v_defEqI_903_ = lean_ctor_get(v___x_895_, 7);
v_extensions_904_ = lean_ctor_get(v___x_895_, 8);
v_issues_905_ = lean_ctor_get(v___x_895_, 9);
v_canon_906_ = lean_ctor_get(v___x_895_, 10);
v_instanceOverrides_907_ = lean_ctor_get(v___x_895_, 11);
v_debug_908_ = lean_ctor_get_uint8(v___x_895_, sizeof(void*)*12);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_919_ == 0)
{
v___x_910_ = v___x_895_;
v_isShared_911_ = v_isSharedCheck_919_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_instanceOverrides_907_);
lean_inc(v_canon_906_);
lean_inc(v_issues_905_);
lean_inc(v_extensions_904_);
lean_inc(v_defEqI_903_);
lean_inc(v_congrInfo_902_);
lean_inc(v_getLevel_901_);
lean_inc(v_inferType_900_);
lean_inc(v_proofInstInfoFVar_899_);
lean_inc(v_proofInstInfo_898_);
lean_inc(v_maxFVar_897_);
lean_inc(v_share_896_);
lean_dec(v___x_895_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_919_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_912_ = lean_box(0);
v___x_913_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(v_instanceOverrides_907_, v_type_891_, v_inst_892_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 11, v___x_913_);
v___x_915_ = v___x_910_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_share_896_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_maxFVar_897_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_proofInstInfo_898_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_proofInstInfoFVar_899_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_inferType_900_);
lean_ctor_set(v_reuseFailAlloc_918_, 5, v_getLevel_901_);
lean_ctor_set(v_reuseFailAlloc_918_, 6, v_congrInfo_902_);
lean_ctor_set(v_reuseFailAlloc_918_, 7, v_defEqI_903_);
lean_ctor_set(v_reuseFailAlloc_918_, 8, v_extensions_904_);
lean_ctor_set(v_reuseFailAlloc_918_, 9, v_issues_905_);
lean_ctor_set(v_reuseFailAlloc_918_, 10, v_canon_906_);
lean_ctor_set(v_reuseFailAlloc_918_, 11, v___x_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_918_, sizeof(void*)*12, v_debug_908_);
v___x_915_ = v_reuseFailAlloc_918_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_st_ref_put(v_a_893_, v___x_915_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_912_);
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___redArg___boxed(lean_object* v_type_920_, lean_object* v_inst_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Meta_Sym_registerInstance___redArg(v_type_920_, v_inst_921_, v_a_922_);
lean_dec(v_a_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance(lean_object* v_type_925_, lean_object* v_inst_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Meta_Sym_registerInstance___redArg(v_type_925_, v_inst_926_, v_a_928_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___boxed(lean_object* v_type_935_, lean_object* v_inst_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_Sym_registerInstance(v_type_935_, v_inst_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0(lean_object* v_00_u03b2_945_, lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_x_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(v_x_946_, v_x_947_, v_x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0(lean_object* v_00_u03b2_950_, lean_object* v_x_951_, size_t v_x_952_, size_t v_x_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_951_, v_x_952_, v_x_953_, v_x_954_, v_x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___boxed(lean_object* v_00_u03b2_957_, lean_object* v_x_958_, lean_object* v_x_959_, lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
size_t v_x_943__boxed_963_; size_t v_x_944__boxed_964_; lean_object* v_res_965_; 
v_x_943__boxed_963_ = lean_unbox_usize(v_x_959_);
lean_dec(v_x_959_);
v_x_944__boxed_964_ = lean_unbox_usize(v_x_960_);
lean_dec(v_x_960_);
v_res_965_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0(v_00_u03b2_957_, v_x_958_, v_x_943__boxed_963_, v_x_944__boxed_964_, v_x_961_, v_x_962_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_966_, lean_object* v_n_967_, lean_object* v_k_968_, lean_object* v_v_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(v_n_967_, v_k_968_, v_v_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_971_, size_t v_depth_972_, lean_object* v_keys_973_, lean_object* v_vals_974_, lean_object* v_heq_975_, lean_object* v_i_976_, lean_object* v_entries_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_depth_972_, v_keys_973_, v_vals_974_, v_i_976_, v_entries_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_979_, lean_object* v_depth_980_, lean_object* v_keys_981_, lean_object* v_vals_982_, lean_object* v_heq_983_, lean_object* v_i_984_, lean_object* v_entries_985_){
_start:
{
size_t v_depth_boxed_986_; lean_object* v_res_987_; 
v_depth_boxed_986_ = lean_unbox_usize(v_depth_980_);
lean_dec(v_depth_980_);
v_res_987_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2(v_00_u03b2_979_, v_depth_boxed_986_, v_keys_981_, v_vals_982_, v_heq_983_, v_i_984_, v_entries_985_);
lean_dec_ref(v_vals_982_);
lean_dec_ref(v_keys_981_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_988_, lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_x_989_, v_x_990_, v_x_991_, v_x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_994_, lean_object* v_vals_995_, lean_object* v_i_996_, lean_object* v_k_997_){
_start:
{
lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = lean_array_get_size(v_keys_994_);
v___x_999_ = lean_nat_dec_lt(v_i_996_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
lean_dec(v_i_996_);
v___x_1000_ = lean_box(0);
return v___x_1000_;
}
else
{
lean_object* v_k_x27_1001_; uint8_t v___x_1002_; 
v_k_x27_1001_ = lean_array_fget_borrowed(v_keys_994_, v_i_996_);
v___x_1002_ = lean_expr_eqv(v_k_997_, v_k_x27_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_unsigned_to_nat(1u);
v___x_1004_ = lean_nat_add(v_i_996_, v___x_1003_);
lean_dec(v_i_996_);
v_i_996_ = v___x_1004_;
goto _start;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_array_fget_borrowed(v_vals_995_, v_i_996_);
lean_dec(v_i_996_);
lean_inc(v___x_1006_);
v___x_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1008_, lean_object* v_vals_1009_, lean_object* v_i_1010_, lean_object* v_k_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1008_, v_vals_1009_, v_i_1010_, v_k_1011_);
lean_dec_ref(v_k_1011_);
lean_dec_ref(v_vals_1009_);
lean_dec_ref(v_keys_1008_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(lean_object* v_x_1013_, size_t v_x_1014_, lean_object* v_x_1015_){
_start:
{
if (lean_obj_tag(v_x_1013_) == 0)
{
lean_object* v_es_1016_; lean_object* v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; lean_object* v_j_1020_; lean_object* v___x_1021_; 
v_es_1016_ = lean_ctor_get(v_x_1013_, 0);
v___x_1017_ = lean_box(2);
v___x_1018_ = ((size_t)31ULL);
v___x_1019_ = lean_usize_land(v_x_1014_, v___x_1018_);
v_j_1020_ = lean_usize_to_nat(v___x_1019_);
v___x_1021_ = lean_array_get_borrowed(v___x_1017_, v_es_1016_, v_j_1020_);
lean_dec(v_j_1020_);
switch(lean_obj_tag(v___x_1021_))
{
case 0:
{
lean_object* v_key_1022_; lean_object* v_val_1023_; uint8_t v___x_1024_; 
v_key_1022_ = lean_ctor_get(v___x_1021_, 0);
v_val_1023_ = lean_ctor_get(v___x_1021_, 1);
v___x_1024_ = lean_expr_eqv(v_x_1015_, v_key_1022_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_box(0);
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; 
lean_inc(v_val_1023_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_val_1023_);
return v___x_1026_;
}
}
case 1:
{
lean_object* v_node_1027_; size_t v___x_1028_; size_t v___x_1029_; 
v_node_1027_ = lean_ctor_get(v___x_1021_, 0);
v___x_1028_ = ((size_t)5ULL);
v___x_1029_ = lean_usize_shift_right(v_x_1014_, v___x_1028_);
v_x_1013_ = v_node_1027_;
v_x_1014_ = v___x_1029_;
goto _start;
}
default: 
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_box(0);
return v___x_1031_;
}
}
}
else
{
lean_object* v_ks_1032_; lean_object* v_vs_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_ks_1032_ = lean_ctor_get(v_x_1013_, 0);
v_vs_1033_ = lean_ctor_get(v_x_1013_, 1);
v___x_1034_ = lean_unsigned_to_nat(0u);
v___x_1035_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1032_, v_vs_1033_, v___x_1034_, v_x_1015_);
return v___x_1035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_){
_start:
{
size_t v_x_747__boxed_1039_; lean_object* v_res_1040_; 
v_x_747__boxed_1039_ = lean_unbox_usize(v_x_1037_);
lean_dec(v_x_1037_);
v_res_1040_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_1036_, v_x_747__boxed_1039_, v_x_1038_);
lean_dec_ref(v_x_1038_);
lean_dec_ref(v_x_1036_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
uint64_t v___x_1043_; size_t v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = l_Lean_Expr_hash(v_x_1042_);
v___x_1044_ = lean_uint64_to_usize(v___x_1043_);
v___x_1045_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_1041_, v___x_1044_, v_x_1042_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg___boxed(lean_object* v_x_1046_, lean_object* v_x_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_x_1046_, v_x_1047_);
lean_dec_ref(v_x_1047_);
lean_dec_ref(v_x_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object* v_type_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1056_; lean_object* v_instanceOverrides_1057_; lean_object* v___x_1058_; 
v___x_1056_ = lean_st_ref_get(v_a_1050_);
v_instanceOverrides_1057_ = lean_ctor_get(v___x_1056_, 11);
lean_inc_ref(v_instanceOverrides_1057_);
lean_dec(v___x_1056_);
v___x_1058_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_instanceOverrides_1057_, v_type_1049_);
lean_dec_ref(v_instanceOverrides_1057_);
if (lean_obj_tag(v___x_1058_) == 1)
{
lean_object* v___x_1059_; 
lean_dec_ref(v_type_1049_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; 
lean_dec(v___x_1058_);
v___x_1060_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg___boxed(lean_object* v_type_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f(lean_object* v_type_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1069_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___boxed(lean_object* v_type_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Meta_Sym_synthInstance_x3f(v_type_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0(lean_object* v_00_u03b2_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_x_1088_, v_x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___boxed(lean_object* v_00_u03b2_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0(v_00_u03b2_1091_, v_x_1092_, v_x_1093_);
lean_dec_ref(v_x_1093_);
lean_dec_ref(v_x_1092_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1095_, lean_object* v_x_1096_, size_t v_x_1097_, lean_object* v_x_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_1096_, v_x_1097_, v_x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
size_t v_x_831__boxed_1104_; lean_object* v_res_1105_; 
v_x_831__boxed_1104_ = lean_unbox_usize(v_x_1102_);
lean_dec(v_x_1102_);
v_res_1105_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0(v_00_u03b2_1100_, v_x_1101_, v_x_831__boxed_1104_, v_x_1103_);
lean_dec_ref(v_x_1103_);
lean_dec_ref(v_x_1101_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1106_, lean_object* v_keys_1107_, lean_object* v_vals_1108_, lean_object* v_heq_1109_, lean_object* v_i_1110_, lean_object* v_k_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1107_, v_vals_1108_, v_i_1110_, v_k_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1113_, lean_object* v_keys_1114_, lean_object* v_vals_1115_, lean_object* v_heq_1116_, lean_object* v_i_1117_, lean_object* v_k_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1113_, v_keys_1114_, v_vals_1115_, v_heq_1116_, v_i_1117_, v_k_1118_);
lean_dec_ref(v_k_1118_);
lean_dec_ref(v_vals_1115_);
lean_dec_ref(v_keys_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(lean_object* v_msgData_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; lean_object* v_env_1127_; uint8_t v___x_1128_; lean_object* v_env_1129_; lean_object* v___x_1130_; lean_object* v_toCold_1131_; lean_object* v_mctx_1132_; lean_object* v_lctx_1133_; lean_object* v_options_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1126_ = lean_st_ref_get(v___y_1124_);
v_env_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc_ref(v_env_1127_);
lean_dec(v___x_1126_);
v___x_1128_ = 0;
v_env_1129_ = l_Lean_Environment_setRecordingDeps(v_env_1127_, v___x_1128_);
v___x_1130_ = lean_st_ref_get(v___y_1122_);
v_toCold_1131_ = lean_ctor_get(v___y_1123_, 0);
v_mctx_1132_ = lean_ctor_get(v___x_1130_, 0);
lean_inc_ref(v_mctx_1132_);
lean_dec(v___x_1130_);
v_lctx_1133_ = lean_ctor_get(v___y_1121_, 2);
v_options_1134_ = lean_ctor_get(v_toCold_1131_, 2);
lean_inc_ref(v_options_1134_);
lean_inc_ref(v_lctx_1133_);
v___x_1135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1135_, 0, v_env_1129_);
lean_ctor_set(v___x_1135_, 1, v_mctx_1132_);
lean_ctor_set(v___x_1135_, 2, v_lctx_1133_);
lean_ctor_set(v___x_1135_, 3, v_options_1134_);
v___x_1136_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v_msgData_1120_);
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0___boxed(lean_object* v_msgData_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(v_msgData_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(lean_object* v_msg_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_ref_1151_; lean_object* v___x_1152_; lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1161_; 
v_ref_1151_ = lean_ctor_get(v___y_1148_, 2);
v___x_1152_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(v_msg_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_inc(v_ref_1151_);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_ref_1151_);
lean_ctor_set(v___x_1157_, 1, v_a_1153_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set_tag(v___x_1155_, 1);
lean_ctor_set(v___x_1155_, 0, v___x_1157_);
v___x_1159_ = v___x_1155_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg___boxed(lean_object* v_msg_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v_msg_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
return v_res_1168_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_synthInstance___closed__1(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l_Lean_Meta_Sym_synthInstance___closed__0));
v___x_1171_ = l_Lean_stringToMessageData(v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance(lean_object* v_type_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1180_; 
lean_inc_ref(v_type_1172_);
v___x_1180_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1172_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1193_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1193_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1193_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
if (lean_obj_tag(v_a_1181_) == 1)
{
lean_object* v_val_1185_; lean_object* v___x_1187_; 
lean_dec_ref(v_type_1172_);
v_val_1185_ = lean_ctor_get(v_a_1181_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v_a_1181_, 1);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v_val_1185_);
v___x_1187_ = v___x_1183_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_val_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_del_object(v___x_1183_);
lean_dec(v_a_1181_);
v___x_1189_ = lean_obj_once(&l_Lean_Meta_Sym_synthInstance___closed__1, &l_Lean_Meta_Sym_synthInstance___closed__1_once, _init_l_Lean_Meta_Sym_synthInstance___closed__1);
v___x_1190_ = l_Lean_indentExpr(v_type_1172_);
v___x_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v___x_1191_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
return v___x_1192_;
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v_type_1172_);
v_a_1194_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1180_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1180_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance___boxed(lean_object* v_type_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Meta_Sym_synthInstance(v_type_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0(lean_object* v_00_u03b1_1211_, lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v_msg_1212_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___boxed(lean_object* v_00_u03b1_1221_, lean_object* v_msg_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0(v_00_u03b1_1221_, v_msg_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(lean_object* v_x_1231_, lean_object* v_type_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1251_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1251_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1251_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
if (lean_obj_tag(v_a_1240_) == 1)
{
lean_object* v_val_1244_; lean_object* v___x_1245_; 
lean_del_object(v___x_1242_);
v_val_1244_ = lean_ctor_get(v_a_1240_, 0);
lean_inc(v_val_1244_);
lean_dec_ref_known(v_a_1240_, 1);
v___x_1245_ = l_Lean_Meta_isExprDefEq(v_x_1231_, v_val_1244_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
return v___x_1245_;
}
else
{
uint8_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
lean_dec(v_a_1240_);
lean_dec_ref(v_x_1231_);
v___x_1246_ = 0;
v___x_1247_ = lean_box(v___x_1246_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1247_);
v___x_1249_ = v___x_1242_;
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
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v_x_1231_);
v_a_1252_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1239_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1239_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg___boxed(lean_object* v_x_1260_, lean_object* v_type_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_x_1260_, v_type_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign(lean_object* v_x_1269_, lean_object* v_type_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_x_1269_, v_type_1270_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___boxed(lean_object* v_x_1279_, lean_object* v_type_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Meta_Sym_synthInstanceAndAssign(v_x_1279_, v_type_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
return v_res_1288_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts = _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts();
lean_mark_persistent(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_SynthInstance(builtin);
}
#ifdef __cplusplus
}
#endif
