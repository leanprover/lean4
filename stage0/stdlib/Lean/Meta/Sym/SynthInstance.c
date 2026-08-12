// Lean compiler output
// Module: Lean.Meta.Sym.SynthInstance
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.SynthInstance import Lean.OrderLevel
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
extern lean_object* l_Lean_Nat_mkInstHMul;
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHAdd;
extern lean_object* l_Lean_Nat_mkInstHSub;
extern lean_object* l_Lean_Nat_mkInstHDiv;
extern lean_object* l_Lean_Nat_mkInstHMod;
extern lean_object* l_Lean_Nat_mkInstHPow;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstLT;
extern lean_object* l_Lean_Nat_mkInstLE;
extern lean_object* l_Lean_Int_mkInstHAdd;
extern lean_object* l_Lean_Int_mkInstHSub;
extern lean_object* l_Lean_Int_mkInstHMul;
extern lean_object* l_Lean_Int_mkInstHDiv;
extern lean_object* l_Lean_Int_mkInstHMod;
extern lean_object* l_Lean_Int_mkInstHPow;
extern lean_object* l_Lean_Int_mkInstLT;
extern lean_object* l_Lean_Int_mkInstLE;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Meta_synthInstanceCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isDefEqStuckExceptionId;
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__3_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__7;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__8_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__11;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__12;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__13_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__17;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__18_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__19_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__22;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__23 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__23_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__24 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__24_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__26;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__27;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__28 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__28_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__29 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__29_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__31;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__32;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__33 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__33_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__34 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__38;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__39;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__40;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__41;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__43;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__44;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__45;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__46;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__48;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__49;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__50;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_29_, lean_object* v_source_30_, lean_object* v_target_31_){
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
v_target_37_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_31_, v_es_34_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2___redArg(lean_object* v_data_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_nbuckets_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_42_ = lean_array_get_size(v_data_41_);
v___x_43_ = lean_unsigned_to_nat(2u);
v_nbuckets_44_ = lean_nat_mul(v___x_42_, v___x_43_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_box(0);
v___x_47_ = lean_mk_array(v_nbuckets_44_, v___x_46_);
v___x_48_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3___redArg(v___x_45_, v_data_41_, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___redArg(lean_object* v_a_49_, lean_object* v_x_50_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 0;
return v___x_51_;
}
else
{
lean_object* v_key_52_; lean_object* v_tail_53_; uint8_t v___x_54_; 
v_key_52_ = lean_ctor_get(v_x_50_, 0);
v_tail_53_ = lean_ctor_get(v_x_50_, 2);
v___x_54_ = lean_expr_eqv(v_key_52_, v_a_49_);
if (v___x_54_ == 0)
{
v_x_50_ = v_tail_53_;
goto _start;
}
else
{
return v___x_54_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_56_, lean_object* v_x_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___redArg(v_a_56_, v_x_57_);
lean_dec(v_x_57_);
lean_dec_ref(v_a_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__3___redArg(lean_object* v_a_60_, lean_object* v_b_61_, lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_62_) == 0)
{
lean_dec(v_b_61_);
lean_dec_ref(v_a_60_);
return v_x_62_;
}
else
{
lean_object* v_key_63_; lean_object* v_value_64_; lean_object* v_tail_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_77_; 
v_key_63_ = lean_ctor_get(v_x_62_, 0);
v_value_64_ = lean_ctor_get(v_x_62_, 1);
v_tail_65_ = lean_ctor_get(v_x_62_, 2);
v_isSharedCheck_77_ = !lean_is_exclusive(v_x_62_);
if (v_isSharedCheck_77_ == 0)
{
v___x_67_ = v_x_62_;
v_isShared_68_ = v_isSharedCheck_77_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_tail_65_);
lean_inc(v_value_64_);
lean_inc(v_key_63_);
lean_dec(v_x_62_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_77_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
uint8_t v___x_69_; 
v___x_69_ = lean_expr_eqv(v_key_63_, v_a_60_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_70_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__3___redArg(v_a_60_, v_b_61_, v_tail_65_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 2, v___x_70_);
v___x_72_ = v___x_67_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_key_63_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_value_64_);
lean_ctor_set(v_reuseFailAlloc_73_, 2, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
else
{
lean_object* v___x_75_; 
lean_dec(v_value_64_);
lean_dec(v_key_63_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v_b_61_);
lean_ctor_set(v___x_67_, 0, v_a_60_);
v___x_75_ = v___x_67_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_a_60_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_b_61_);
lean_ctor_set(v_reuseFailAlloc_76_, 2, v_tail_65_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0___redArg(lean_object* v_m_78_, lean_object* v_a_79_, lean_object* v_b_80_){
_start:
{
lean_object* v_size_81_; lean_object* v_buckets_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_125_; 
v_size_81_ = lean_ctor_get(v_m_78_, 0);
v_buckets_82_ = lean_ctor_get(v_m_78_, 1);
v_isSharedCheck_125_ = !lean_is_exclusive(v_m_78_);
if (v_isSharedCheck_125_ == 0)
{
v___x_84_ = v_m_78_;
v_isShared_85_ = v_isSharedCheck_125_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_buckets_82_);
lean_inc(v_size_81_);
lean_dec(v_m_78_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_125_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; uint64_t v___x_87_; uint64_t v___x_88_; uint64_t v___x_89_; uint64_t v_fold_90_; uint64_t v___x_91_; uint64_t v___x_92_; uint64_t v___x_93_; size_t v___x_94_; size_t v___x_95_; size_t v___x_96_; size_t v___x_97_; size_t v___x_98_; lean_object* v_bkt_99_; uint8_t v___x_100_; 
v___x_86_ = lean_array_get_size(v_buckets_82_);
v___x_87_ = l_Lean_Expr_hash(v_a_79_);
v___x_88_ = 32ULL;
v___x_89_ = lean_uint64_shift_right(v___x_87_, v___x_88_);
v_fold_90_ = lean_uint64_xor(v___x_87_, v___x_89_);
v___x_91_ = 16ULL;
v___x_92_ = lean_uint64_shift_right(v_fold_90_, v___x_91_);
v___x_93_ = lean_uint64_xor(v_fold_90_, v___x_92_);
v___x_94_ = lean_uint64_to_usize(v___x_93_);
v___x_95_ = lean_usize_of_nat(v___x_86_);
v___x_96_ = ((size_t)1ULL);
v___x_97_ = lean_usize_sub(v___x_95_, v___x_96_);
v___x_98_ = lean_usize_land(v___x_94_, v___x_97_);
v_bkt_99_ = lean_array_uget_borrowed(v_buckets_82_, v___x_98_);
v___x_100_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___redArg(v_a_79_, v_bkt_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v_size_x27_102_; lean_object* v___x_103_; lean_object* v_buckets_x27_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v_size_x27_102_ = lean_nat_add(v_size_81_, v___x_101_);
lean_dec(v_size_81_);
lean_inc(v_bkt_99_);
v___x_103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_103_, 0, v_a_79_);
lean_ctor_set(v___x_103_, 1, v_b_80_);
lean_ctor_set(v___x_103_, 2, v_bkt_99_);
v_buckets_x27_104_ = lean_array_uset(v_buckets_82_, v___x_98_, v___x_103_);
v___x_105_ = lean_unsigned_to_nat(4u);
v___x_106_ = lean_nat_mul(v_size_x27_102_, v___x_105_);
v___x_107_ = lean_unsigned_to_nat(3u);
v___x_108_ = lean_nat_div(v___x_106_, v___x_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_array_get_size(v_buckets_x27_104_);
v___x_110_ = lean_nat_dec_le(v___x_108_, v___x_109_);
lean_dec(v___x_108_);
if (v___x_110_ == 0)
{
lean_object* v_val_111_; lean_object* v___x_113_; 
v_val_111_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2___redArg(v_buckets_x27_104_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v_val_111_);
lean_ctor_set(v___x_84_, 0, v_size_x27_102_);
v___x_113_ = v___x_84_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_size_x27_102_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_val_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
else
{
lean_object* v___x_116_; 
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v_buckets_x27_104_);
lean_ctor_set(v___x_84_, 0, v_size_x27_102_);
v___x_116_ = v___x_84_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_size_x27_102_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_buckets_x27_104_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
else
{
lean_object* v___x_118_; lean_object* v_buckets_x27_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
lean_inc(v_bkt_99_);
v___x_118_ = lean_box(0);
v_buckets_x27_119_ = lean_array_uset(v_buckets_82_, v___x_98_, v___x_118_);
v___x_120_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__3___redArg(v_a_79_, v_b_80_, v_bkt_99_);
v___x_121_ = lean_array_uset(v_buckets_x27_119_, v___x_98_, v___x_120_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___x_121_);
v___x_123_ = v___x_84_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_size_81_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg(lean_object* v_as_x27_126_, lean_object* v_b_127_){
_start:
{
if (lean_obj_tag(v_as_x27_126_) == 0)
{
return v_b_127_;
}
else
{
lean_object* v_head_128_; lean_object* v_tail_129_; lean_object* v_fst_130_; lean_object* v_snd_131_; lean_object* v_r_132_; 
v_head_128_ = lean_ctor_get(v_as_x27_126_, 0);
v_tail_129_ = lean_ctor_get(v_as_x27_126_, 1);
v_fst_130_ = lean_ctor_get(v_head_128_, 0);
v_snd_131_ = lean_ctor_get(v_head_128_, 1);
lean_inc(v_snd_131_);
lean_inc(v_fst_130_);
v_r_132_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0___redArg(v_b_127_, v_fst_130_, v_snd_131_);
v_as_x27_126_ = v_tail_129_;
v_b_127_ = v_r_132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_134_, lean_object* v_b_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg(v_as_x27_134_, v_b_135_);
lean_dec(v_as_x27_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0(lean_object* v_m_137_, lean_object* v_l_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg(v_l_138_, v_m_137_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0___boxed(lean_object* v_m_140_, lean_object* v_l_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0(v_m_140_, v_l_141_);
lean_dec(v_l_141_);
return v_res_142_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5(void){
_start:
{
lean_object* v_us_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_us_155_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2));
v___x_156_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__4));
v___x_157_ = l_Lean_mkConst(v___x_156_, v_us_155_);
return v___x_157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__6(void){
_start:
{
lean_object* v_nat_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_nat_158_ = l_Lean_Nat_mkType;
v___x_159_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5);
v___x_160_ = l_Lean_mkApp3(v___x_159_, v_nat_158_, v_nat_158_, v_nat_158_);
return v___x_160_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__7(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = l_Lean_Nat_mkInstHAdd;
v___x_162_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__6, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__6_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__6);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10(void){
_start:
{
lean_object* v_us_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_us_167_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2));
v___x_168_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__9));
v___x_169_ = l_Lean_mkConst(v___x_168_, v_us_167_);
return v___x_169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__11(void){
_start:
{
lean_object* v_nat_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_nat_170_ = l_Lean_Nat_mkType;
v___x_171_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10);
v___x_172_ = l_Lean_mkApp3(v___x_171_, v_nat_170_, v_nat_170_, v_nat_170_);
return v___x_172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__12(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = l_Lean_Nat_mkInstHSub;
v___x_174_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__11, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__11_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__11);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
return v___x_175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15(void){
_start:
{
lean_object* v_us_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_us_179_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2));
v___x_180_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__14));
v___x_181_ = l_Lean_mkConst(v___x_180_, v_us_179_);
return v___x_181_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__16(void){
_start:
{
lean_object* v_nat_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_nat_182_ = l_Lean_Nat_mkType;
v___x_183_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15);
v___x_184_ = l_Lean_mkApp3(v___x_183_, v_nat_182_, v_nat_182_, v_nat_182_);
return v___x_184_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__17(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = l_Lean_Nat_mkInstHMul;
v___x_186_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__16, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__16_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__16);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20(void){
_start:
{
lean_object* v_us_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_us_191_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2));
v___x_192_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__19));
v___x_193_ = l_Lean_mkConst(v___x_192_, v_us_191_);
return v___x_193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__21(void){
_start:
{
lean_object* v_nat_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_nat_194_ = l_Lean_Nat_mkType;
v___x_195_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20);
v___x_196_ = l_Lean_mkApp3(v___x_195_, v_nat_194_, v_nat_194_, v_nat_194_);
return v___x_196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__22(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = l_Lean_Nat_mkInstHDiv;
v___x_198_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__21, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__21_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__21);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25(void){
_start:
{
lean_object* v_us_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_us_203_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2));
v___x_204_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__24));
v___x_205_ = l_Lean_mkConst(v___x_204_, v_us_203_);
return v___x_205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__26(void){
_start:
{
lean_object* v_nat_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_nat_206_ = l_Lean_Nat_mkType;
v___x_207_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25);
v___x_208_ = l_Lean_mkApp3(v___x_207_, v_nat_206_, v_nat_206_, v_nat_206_);
return v___x_208_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__27(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = l_Lean_Nat_mkInstHMod;
v___x_210_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__26, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__26_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__26);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30(void){
_start:
{
lean_object* v_us_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_us_215_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2));
v___x_216_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__29));
v___x_217_ = l_Lean_mkConst(v___x_216_, v_us_215_);
return v___x_217_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__31(void){
_start:
{
lean_object* v_nat_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_nat_218_ = l_Lean_Nat_mkType;
v___x_219_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30);
v___x_220_ = l_Lean_mkApp3(v___x_219_, v_nat_218_, v_nat_218_, v_nat_218_);
return v___x_220_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__32(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = l_Lean_Nat_mkInstHPow;
v___x_222_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__31, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__31_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__31);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
return v___x_223_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37(void){
_start:
{
lean_object* v_int_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_int_230_ = l_Lean_Int_mkType;
v___x_231_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5);
v___x_232_ = l_Lean_mkApp3(v___x_231_, v_int_230_, v_int_230_, v_int_230_);
return v___x_232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__38(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = l_Lean_Int_mkInstHAdd;
v___x_234_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_233_);
return v___x_235_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__39(void){
_start:
{
lean_object* v_int_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_int_236_ = l_Lean_Int_mkType;
v___x_237_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10);
v___x_238_ = l_Lean_mkApp3(v___x_237_, v_int_236_, v_int_236_, v_int_236_);
return v___x_238_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__40(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = l_Lean_Int_mkInstHSub;
v___x_240_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__39, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__39_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__39);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__41(void){
_start:
{
lean_object* v_int_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_int_242_ = l_Lean_Int_mkType;
v___x_243_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15);
v___x_244_ = l_Lean_mkApp3(v___x_243_, v_int_242_, v_int_242_, v_int_242_);
return v___x_244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = l_Lean_Int_mkInstHMul;
v___x_246_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__41, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__41_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__41);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_245_);
return v___x_247_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__43(void){
_start:
{
lean_object* v_int_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_int_248_ = l_Lean_Int_mkType;
v___x_249_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20);
v___x_250_ = l_Lean_mkApp3(v___x_249_, v_int_248_, v_int_248_, v_int_248_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__44(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = l_Lean_Int_mkInstHDiv;
v___x_252_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__43, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__43_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__43);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__45(void){
_start:
{
lean_object* v_int_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_int_254_ = l_Lean_Int_mkType;
v___x_255_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25);
v___x_256_ = l_Lean_mkApp3(v___x_255_, v_int_254_, v_int_254_, v_int_254_);
return v___x_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__46(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = l_Lean_Int_mkInstHMod;
v___x_258_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__45, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__45_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__45);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47(void){
_start:
{
lean_object* v_nat_260_; lean_object* v_int_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_nat_260_ = l_Lean_Nat_mkType;
v_int_261_ = l_Lean_Int_mkType;
v___x_262_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30);
v___x_263_ = l_Lean_mkApp3(v___x_262_, v_int_261_, v_nat_260_, v_int_261_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__48(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = l_Lean_Int_mkInstHPow;
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__49(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_box(0);
v___x_268_ = lean_unsigned_to_nat(16u);
v___x_269_ = lean_mk_array(v___x_268_, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__50(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__49, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__49_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__49);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts(lean_object* v_leLvl_273_){
_start:
{
lean_object* v_nat_274_; lean_object* v_int_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_nat_274_ = l_Lean_Nat_mkType;
v_int_275_ = l_Lean_Int_mkType;
v___x_276_ = lean_box(0);
v___x_277_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__7, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__7_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__7);
v___x_278_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__12, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__12_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__12);
v___x_279_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__17, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__17_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__17);
v___x_280_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__22, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__22_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__22);
v___x_281_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__27, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__27_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__27);
v___x_282_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__32, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__32_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__32);
v___x_283_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__34));
v___x_284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_284_, 0, v_leLvl_273_);
lean_ctor_set(v___x_284_, 1, v___x_276_);
lean_inc_ref(v___x_284_);
v___x_285_ = l_Lean_mkConst(v___x_283_, v___x_284_);
lean_inc_ref(v___x_285_);
v___x_286_ = l_Lean_Expr_app___override(v___x_285_, v_nat_274_);
v___x_287_ = l_Lean_Nat_mkInstLT;
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36));
v___x_290_ = l_Lean_mkConst(v___x_289_, v___x_284_);
lean_inc_ref(v___x_290_);
v___x_291_ = l_Lean_Expr_app___override(v___x_290_, v_nat_274_);
v___x_292_ = l_Lean_Nat_mkInstLE;
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__38, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__38_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__38);
v___x_295_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__40, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__40_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__40);
v___x_296_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42);
v___x_297_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__44, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__44_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__44);
v___x_298_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__46, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__46_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__46);
v___x_299_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__48, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__48_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__48);
v___x_300_ = l_Lean_Expr_app___override(v___x_285_, v_int_275_);
v___x_301_ = l_Lean_Int_mkInstLT;
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = l_Lean_Expr_app___override(v___x_290_, v_int_275_);
v___x_304_ = l_Lean_Int_mkInstLE;
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_276_);
v___x_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_302_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_299_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_298_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_297_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_296_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_295_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_294_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_293_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_288_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_282_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_281_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_280_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_279_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_278_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_277_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__50, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__50_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__50);
v___x_323_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg(v___x_321_, v___x_322_);
lean_dec_ref_known(v___x_321_, 2);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0(lean_object* v_00_u03b2_324_, lean_object* v_m_325_, lean_object* v_a_326_, lean_object* v_b_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0___redArg(v_m_325_, v_a_326_, v_b_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1(lean_object* v_as_329_, lean_object* v_as_x27_330_, lean_object* v_b_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg(v_as_x27_330_, v_b_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___boxed(lean_object* v_as_334_, lean_object* v_as_x27_335_, lean_object* v_b_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1(v_as_334_, v_as_x27_335_, v_b_336_, v_a_337_);
lean_dec(v_as_x27_335_);
lean_dec(v_as_334_);
return v_res_338_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_339_, lean_object* v_a_340_, lean_object* v_x_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___redArg(v_a_340_, v_x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_343_, lean_object* v_a_344_, lean_object* v_x_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1(v_00_u03b2_343_, v_a_344_, v_x_345_);
lean_dec(v_x_345_);
lean_dec_ref(v_a_344_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_348_, lean_object* v_data_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2___redArg(v_data_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_351_, lean_object* v_a_352_, lean_object* v_b_353_, lean_object* v_x_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__3___redArg(v_a_352_, v_b_353_, v_x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_356_, lean_object* v_i_357_, lean_object* v_source_358_, lean_object* v_target_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3___redArg(v_i_357_, v_source_358_, v_target_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_362_, v_x_363_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier___closed__0(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_box(0);
v___x_366_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts(v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier(void){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier___closed__0, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier___closed__0_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier___closed__0);
return v___x_367_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__0(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_box(0);
v___x_369_ = l_Lean_Level_succ___override(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__1(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__0, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__0_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__0);
v___x_371_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__1, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__1_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__1);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(lean_object* v_a_373_, lean_object* v_x_374_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
lean_object* v___x_375_; 
v___x_375_ = lean_box(0);
return v___x_375_;
}
else
{
lean_object* v_key_376_; lean_object* v_value_377_; lean_object* v_tail_378_; uint8_t v___x_379_; 
v_key_376_ = lean_ctor_get(v_x_374_, 0);
v_value_377_ = lean_ctor_get(v_x_374_, 1);
v_tail_378_ = lean_ctor_get(v_x_374_, 2);
v___x_379_ = lean_expr_eqv(v_key_376_, v_a_373_);
if (v___x_379_ == 0)
{
v_x_374_ = v_tail_378_;
goto _start;
}
else
{
lean_object* v___x_381_; 
lean_inc(v_value_377_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v_value_377_);
return v___x_381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_382_, lean_object* v_x_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(v_a_382_, v_x_383_);
lean_dec(v_x_383_);
lean_dec_ref(v_a_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(lean_object* v_m_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_buckets_387_; lean_object* v___x_388_; uint64_t v___x_389_; uint64_t v___x_390_; uint64_t v___x_391_; uint64_t v_fold_392_; uint64_t v___x_393_; uint64_t v___x_394_; uint64_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_buckets_387_ = lean_ctor_get(v_m_385_, 1);
v___x_388_ = lean_array_get_size(v_buckets_387_);
v___x_389_ = l_Lean_Expr_hash(v_a_386_);
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
v___x_401_ = lean_array_uget_borrowed(v_buckets_387_, v___x_400_);
v___x_402_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(v_a_386_, v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg___boxed(lean_object* v_m_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v_m_403_, v_a_404_);
lean_dec_ref(v_a_404_);
lean_dec_ref(v_m_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f(uint8_t v_leCarrierIsSort_406_, lean_object* v_type_407_){
_start:
{
if (v_leCarrierIsSort_406_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier;
v___x_409_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v___x_408_, v_type_407_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier;
v___x_411_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v___x_410_, v_type_407_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___boxed(lean_object* v_leCarrierIsSort_412_, lean_object* v_type_413_){
_start:
{
uint8_t v_leCarrierIsSort_boxed_414_; lean_object* v_res_415_; 
v_leCarrierIsSort_boxed_414_ = lean_unbox(v_leCarrierIsSort_412_);
v_res_415_ = l_Lean_Meta_Sym_getBuiltinInstance_x3f(v_leCarrierIsSort_boxed_414_, v_type_413_);
lean_dec_ref(v_type_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0(lean_object* v_00_u03b2_416_, lean_object* v_m_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v_m_417_, v_a_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___boxed(lean_object* v_00_u03b2_420_, lean_object* v_m_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0(v_00_u03b2_420_, v_m_421_, v_a_422_);
lean_dec_ref(v_a_422_);
lean_dec_ref(v_m_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0(lean_object* v_00_u03b2_424_, lean_object* v_a_425_, lean_object* v_x_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(v_a_425_, v_x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_428_, lean_object* v_a_429_, lean_object* v_x_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0(v_00_u03b2_428_, v_a_429_, v_x_430_);
lean_dec(v_x_430_);
lean_dec_ref(v_a_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(lean_object* v_category_432_, lean_object* v_opts_433_, lean_object* v_act_434_, lean_object* v_decl_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_inc(v___y_439_);
lean_inc_ref(v___y_438_);
lean_inc(v___y_437_);
lean_inc_ref(v___y_436_);
v___x_441_ = lean_apply_4(v_act_434_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
v___x_442_ = l_Lean_profileitIOUnsafe___redArg(v_category_432_, v_opts_433_, v___x_441_, v_decl_435_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg___boxed(lean_object* v_category_443_, lean_object* v_opts_444_, lean_object* v_act_445_, lean_object* v_decl_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v_category_443_, v_opts_444_, v_act_445_, v_decl_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec_ref(v_opts_444_);
lean_dec_ref(v_category_443_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(lean_object* v_00_u03b1_453_, lean_object* v_category_454_, lean_object* v_opts_455_, lean_object* v_act_456_, lean_object* v_decl_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v_category_454_, v_opts_455_, v_act_456_, v_decl_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___boxed(lean_object* v_00_u03b1_464_, lean_object* v_category_465_, lean_object* v_opts_466_, lean_object* v_act_467_, lean_object* v_decl_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(v_00_u03b1_464_, v_category_465_, v_opts_466_, v_act_467_, v_decl_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec_ref(v_opts_466_);
lean_dec_ref(v_category_465_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(lean_object* v_type_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_leCarrierIsSort(v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_509_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_509_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_509_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_509_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
uint8_t v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_unbox(v_a_482_);
lean_dec(v_a_482_);
v___x_487_ = l_Lean_Meta_Sym_getBuiltinInstance_x3f(v___x_486_, v_type_475_);
if (lean_obj_tag(v___x_487_) == 1)
{
lean_object* v___x_489_; 
lean_dec_ref(v_type_475_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_487_);
v___x_489_ = v___x_484_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v___x_487_);
lean_del_object(v___x_484_);
v___x_491_ = lean_box(0);
v___x_492_ = l_Lean_Meta_synthInstanceCore_x3f(v_type_475_, v___x_491_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_492_) == 0)
{
return v___x_492_;
}
else
{
lean_object* v_a_493_; lean_object* v___x_494_; uint8_t v___y_496_; uint8_t v___x_507_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
v___x_494_ = l_Lean_Meta_isDefEqStuckExceptionId;
v___x_507_ = l_Lean_Exception_isInterrupt(v_a_493_);
if (v___x_507_ == 0)
{
uint8_t v___x_508_; 
lean_inc(v_a_493_);
v___x_508_ = l_Lean_Exception_isRuntime(v_a_493_);
v___y_496_ = v___x_508_;
goto v___jp_495_;
}
else
{
v___y_496_ = v___x_507_;
goto v___jp_495_;
}
v___jp_495_:
{
if (v___y_496_ == 0)
{
if (lean_obj_tag(v_a_493_) == 0)
{
lean_dec_ref_known(v_a_493_, 2);
return v___x_492_;
}
else
{
lean_object* v_id_497_; uint8_t v___x_498_; 
v_id_497_ = lean_ctor_get(v_a_493_, 0);
lean_inc(v_id_497_);
lean_dec_ref_known(v_a_493_, 2);
v___x_498_ = l_Lean_instBEqInternalExceptionId_beq(v___x_494_, v_id_497_);
lean_dec(v_id_497_);
if (v___x_498_ == 0)
{
return v___x_492_;
}
else
{
lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v___x_492_, 0);
lean_dec(v_unused_506_);
v___x_500_ = v___x_492_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_dec(v___x_492_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 0);
lean_ctor_set(v___x_500_, 0, v___x_491_);
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_491_);
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
}
else
{
lean_dec(v_a_493_);
return v___x_492_;
}
}
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v_type_475_);
v_a_510_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_481_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_481_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed(lean_object* v_type_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(v_type_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object* v_type_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_options_532_; lean_object* v___f_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_options_532_ = lean_ctor_get(v_a_529_, 2);
lean_inc_ref(v_type_526_);
v___f_533_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_533_, 0, v_type_526_);
v___x_534_ = ((lean_object*)(l_Lean_Meta_Sym_synthInstanceMeta_x3f___closed__0));
v___x_535_ = l_Lean_Expr_getAppFn(v_type_526_);
lean_dec_ref(v_type_526_);
v___x_536_ = l_Lean_Expr_constName_x3f(v___x_535_);
lean_dec_ref(v___x_535_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_box(0);
v___x_538_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v___x_534_, v_options_532_, v___f_533_, v___x_537_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
return v___x_538_;
}
else
{
lean_object* v_val_539_; lean_object* v___x_540_; 
v_val_539_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_val_539_);
lean_dec_ref_known(v___x_536_, 1);
v___x_540_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v___x_534_, v_options_532_, v___f_533_, v_val_539_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___boxed(lean_object* v_type_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_548_, lean_object* v_x_549_, lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
lean_object* v_ks_552_; lean_object* v_vs_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_577_; 
v_ks_552_ = lean_ctor_get(v_x_548_, 0);
v_vs_553_ = lean_ctor_get(v_x_548_, 1);
v_isSharedCheck_577_ = !lean_is_exclusive(v_x_548_);
if (v_isSharedCheck_577_ == 0)
{
v___x_555_ = v_x_548_;
v_isShared_556_ = v_isSharedCheck_577_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_vs_553_);
lean_inc(v_ks_552_);
lean_dec(v_x_548_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_577_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_array_get_size(v_ks_552_);
v___x_558_ = lean_nat_dec_lt(v_x_549_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
lean_dec(v_x_549_);
v___x_559_ = lean_array_push(v_ks_552_, v_x_550_);
v___x_560_ = lean_array_push(v_vs_553_, v_x_551_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v___x_560_);
lean_ctor_set(v___x_555_, 0, v___x_559_);
v___x_562_ = v___x_555_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
else
{
lean_object* v_k_x27_564_; uint8_t v___x_565_; 
v_k_x27_564_ = lean_array_fget_borrowed(v_ks_552_, v_x_549_);
v___x_565_ = lean_expr_eqv(v_x_550_, v_k_x27_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_567_; 
if (v_isShared_556_ == 0)
{
v___x_567_ = v___x_555_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_ks_552_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_vs_553_);
v___x_567_ = v_reuseFailAlloc_571_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_nat_add(v_x_549_, v___x_568_);
lean_dec(v_x_549_);
v_x_548_ = v___x_567_;
v_x_549_ = v___x_569_;
goto _start;
}
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_572_ = lean_array_fset(v_ks_552_, v_x_549_, v_x_550_);
v___x_573_ = lean_array_fset(v_vs_553_, v_x_549_, v_x_551_);
lean_dec(v_x_549_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v___x_573_);
lean_ctor_set(v___x_555_, 0, v___x_572_);
v___x_575_ = v___x_555_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v___x_573_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_n_578_, lean_object* v_k_579_, lean_object* v_v_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_578_, v___x_581_, v_k_579_, v_v_580_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(lean_object* v_x_584_, size_t v_x_585_, size_t v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_object* v_es_589_; size_t v___x_590_; size_t v___x_591_; lean_object* v_j_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_es_589_ = lean_ctor_get(v_x_584_, 0);
v___x_590_ = ((size_t)31ULL);
v___x_591_ = lean_usize_land(v_x_585_, v___x_590_);
v_j_592_ = lean_usize_to_nat(v___x_591_);
v___x_593_ = lean_array_get_size(v_es_589_);
v___x_594_ = lean_nat_dec_lt(v_j_592_, v___x_593_);
if (v___x_594_ == 0)
{
lean_dec(v_j_592_);
lean_dec(v_x_588_);
lean_dec_ref(v_x_587_);
return v_x_584_;
}
else
{
lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_633_; 
lean_inc_ref(v_es_589_);
v_isSharedCheck_633_ = !lean_is_exclusive(v_x_584_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; 
v_unused_634_ = lean_ctor_get(v_x_584_, 0);
lean_dec(v_unused_634_);
v___x_596_ = v_x_584_;
v_isShared_597_ = v_isSharedCheck_633_;
goto v_resetjp_595_;
}
else
{
lean_dec(v_x_584_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_633_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v_v_598_; lean_object* v___x_599_; lean_object* v_xs_x27_600_; lean_object* v___y_602_; 
v_v_598_ = lean_array_fget(v_es_589_, v_j_592_);
v___x_599_ = lean_box(0);
v_xs_x27_600_ = lean_array_fset(v_es_589_, v_j_592_, v___x_599_);
switch(lean_obj_tag(v_v_598_))
{
case 0:
{
lean_object* v_key_607_; lean_object* v_val_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_618_; 
v_key_607_ = lean_ctor_get(v_v_598_, 0);
v_val_608_ = lean_ctor_get(v_v_598_, 1);
v_isSharedCheck_618_ = !lean_is_exclusive(v_v_598_);
if (v_isSharedCheck_618_ == 0)
{
v___x_610_ = v_v_598_;
v_isShared_611_ = v_isSharedCheck_618_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_val_608_);
lean_inc(v_key_607_);
lean_dec(v_v_598_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_618_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
uint8_t v___x_612_; 
v___x_612_ = lean_expr_eqv(v_x_587_, v_key_607_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_del_object(v___x_610_);
v___x_613_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_607_, v_val_608_, v_x_587_, v_x_588_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
v___y_602_ = v___x_614_;
goto v___jp_601_;
}
else
{
lean_object* v___x_616_; 
lean_dec(v_val_608_);
lean_dec(v_key_607_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 1, v_x_588_);
lean_ctor_set(v___x_610_, 0, v_x_587_);
v___x_616_ = v___x_610_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_x_587_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_x_588_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
v___y_602_ = v___x_616_;
goto v___jp_601_;
}
}
}
}
case 1:
{
lean_object* v_node_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_631_; 
v_node_619_ = lean_ctor_get(v_v_598_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v_v_598_);
if (v_isSharedCheck_631_ == 0)
{
v___x_621_ = v_v_598_;
v_isShared_622_ = v_isSharedCheck_631_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_node_619_);
lean_dec(v_v_598_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_631_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
size_t v___x_623_; size_t v___x_624_; size_t v___x_625_; size_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_623_ = ((size_t)5ULL);
v___x_624_ = lean_usize_shift_right(v_x_585_, v___x_623_);
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_add(v_x_586_, v___x_625_);
v___x_627_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_node_619_, v___x_624_, v___x_626_, v_x_587_, v_x_588_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_627_);
v___x_629_ = v___x_621_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
v___y_602_ = v___x_629_;
goto v___jp_601_;
}
}
}
default: 
{
lean_object* v___x_632_; 
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v_x_587_);
lean_ctor_set(v___x_632_, 1, v_x_588_);
v___y_602_ = v___x_632_;
goto v___jp_601_;
}
}
v___jp_601_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = lean_array_fset(v_xs_x27_600_, v_j_592_, v___y_602_);
lean_dec(v_j_592_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_603_);
v___x_605_ = v___x_596_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
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
}
else
{
lean_object* v_ks_635_; lean_object* v_vs_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_656_; 
v_ks_635_ = lean_ctor_get(v_x_584_, 0);
v_vs_636_ = lean_ctor_get(v_x_584_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_x_584_);
if (v_isSharedCheck_656_ == 0)
{
v___x_638_ = v_x_584_;
v_isShared_639_ = v_isSharedCheck_656_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_vs_636_);
lean_inc(v_ks_635_);
lean_dec(v_x_584_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_656_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_ks_635_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_vs_636_);
v___x_641_ = v_reuseFailAlloc_655_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v_newNode_642_; uint8_t v___y_644_; size_t v___x_650_; uint8_t v___x_651_; 
v_newNode_642_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(v___x_641_, v_x_587_, v_x_588_);
v___x_650_ = ((size_t)7ULL);
v___x_651_ = lean_usize_dec_le(v___x_650_, v_x_586_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_652_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_642_);
v___x_653_ = lean_unsigned_to_nat(4u);
v___x_654_ = lean_nat_dec_lt(v___x_652_, v___x_653_);
lean_dec(v___x_652_);
v___y_644_ = v___x_654_;
goto v___jp_643_;
}
else
{
v___y_644_ = v___x_651_;
goto v___jp_643_;
}
v___jp_643_:
{
if (v___y_644_ == 0)
{
lean_object* v_ks_645_; lean_object* v_vs_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_ks_645_ = lean_ctor_get(v_newNode_642_, 0);
lean_inc_ref(v_ks_645_);
v_vs_646_ = lean_ctor_get(v_newNode_642_, 1);
lean_inc_ref(v_vs_646_);
lean_dec_ref(v_newNode_642_);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0);
v___x_649_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_x_586_, v_ks_645_, v_vs_646_, v___x_647_, v___x_648_);
lean_dec_ref(v_vs_646_);
lean_dec_ref(v_ks_645_);
return v___x_649_;
}
else
{
return v_newNode_642_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(size_t v_depth_657_, lean_object* v_keys_658_, lean_object* v_vals_659_, lean_object* v_i_660_, lean_object* v_entries_661_){
_start:
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_array_get_size(v_keys_658_);
v___x_663_ = lean_nat_dec_lt(v_i_660_, v___x_662_);
if (v___x_663_ == 0)
{
lean_dec(v_i_660_);
return v_entries_661_;
}
else
{
lean_object* v_k_664_; lean_object* v_v_665_; uint64_t v___x_666_; size_t v_h_667_; size_t v___x_668_; lean_object* v___x_669_; size_t v___x_670_; size_t v___x_671_; size_t v___x_672_; size_t v_h_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_k_664_ = lean_array_fget_borrowed(v_keys_658_, v_i_660_);
v_v_665_ = lean_array_fget_borrowed(v_vals_659_, v_i_660_);
v___x_666_ = l_Lean_Expr_hash(v_k_664_);
v_h_667_ = lean_uint64_to_usize(v___x_666_);
v___x_668_ = ((size_t)5ULL);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = ((size_t)1ULL);
v___x_671_ = lean_usize_sub(v_depth_657_, v___x_670_);
v___x_672_ = lean_usize_mul(v___x_668_, v___x_671_);
v_h_673_ = lean_usize_shift_right(v_h_667_, v___x_672_);
v___x_674_ = lean_nat_add(v_i_660_, v___x_669_);
lean_dec(v_i_660_);
lean_inc(v_v_665_);
lean_inc(v_k_664_);
v___x_675_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_entries_661_, v_h_673_, v_depth_657_, v_k_664_, v_v_665_);
v_i_660_ = v___x_674_;
v_entries_661_ = v___x_675_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_677_, lean_object* v_keys_678_, lean_object* v_vals_679_, lean_object* v_i_680_, lean_object* v_entries_681_){
_start:
{
size_t v_depth_boxed_682_; lean_object* v_res_683_; 
v_depth_boxed_682_ = lean_unbox_usize(v_depth_677_);
lean_dec(v_depth_677_);
v_res_683_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_depth_boxed_682_, v_keys_678_, v_vals_679_, v_i_680_, v_entries_681_);
lean_dec_ref(v_vals_679_);
lean_dec_ref(v_keys_678_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___boxed(lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
size_t v_x_727__boxed_689_; size_t v_x_728__boxed_690_; lean_object* v_res_691_; 
v_x_727__boxed_689_ = lean_unbox_usize(v_x_685_);
lean_dec(v_x_685_);
v_x_728__boxed_690_ = lean_unbox_usize(v_x_686_);
lean_dec(v_x_686_);
v_res_691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_684_, v_x_727__boxed_689_, v_x_728__boxed_690_, v_x_687_, v_x_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
uint64_t v___x_695_; size_t v___x_696_; size_t v___x_697_; lean_object* v___x_698_; 
v___x_695_ = l_Lean_Expr_hash(v_x_693_);
v___x_696_ = lean_uint64_to_usize(v___x_695_);
v___x_697_ = ((size_t)1ULL);
v___x_698_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_692_, v___x_696_, v___x_697_, v_x_693_, v_x_694_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object* v_type_699_, lean_object* v_inst_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_703_; lean_object* v_share_704_; lean_object* v_maxFVar_705_; lean_object* v_proofInstInfo_706_; lean_object* v_inferType_707_; lean_object* v_getLevel_708_; lean_object* v_congrInfo_709_; lean_object* v_defEqI_710_; lean_object* v_extensions_711_; lean_object* v_issues_712_; lean_object* v_canon_713_; lean_object* v_instanceOverrides_714_; uint8_t v_debug_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_726_; 
v___x_703_ = lean_st_ref_take(v_a_701_);
v_share_704_ = lean_ctor_get(v___x_703_, 0);
v_maxFVar_705_ = lean_ctor_get(v___x_703_, 1);
v_proofInstInfo_706_ = lean_ctor_get(v___x_703_, 2);
v_inferType_707_ = lean_ctor_get(v___x_703_, 3);
v_getLevel_708_ = lean_ctor_get(v___x_703_, 4);
v_congrInfo_709_ = lean_ctor_get(v___x_703_, 5);
v_defEqI_710_ = lean_ctor_get(v___x_703_, 6);
v_extensions_711_ = lean_ctor_get(v___x_703_, 7);
v_issues_712_ = lean_ctor_get(v___x_703_, 8);
v_canon_713_ = lean_ctor_get(v___x_703_, 9);
v_instanceOverrides_714_ = lean_ctor_get(v___x_703_, 10);
v_debug_715_ = lean_ctor_get_uint8(v___x_703_, sizeof(void*)*11);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_726_ == 0)
{
v___x_717_ = v___x_703_;
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_instanceOverrides_714_);
lean_inc(v_canon_713_);
lean_inc(v_issues_712_);
lean_inc(v_extensions_711_);
lean_inc(v_defEqI_710_);
lean_inc(v_congrInfo_709_);
lean_inc(v_getLevel_708_);
lean_inc(v_inferType_707_);
lean_inc(v_proofInstInfo_706_);
lean_inc(v_maxFVar_705_);
lean_inc(v_share_704_);
lean_dec(v___x_703_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(v_instanceOverrides_714_, v_type_699_, v_inst_700_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 10, v___x_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_share_704_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_maxFVar_705_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_proofInstInfo_706_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v_inferType_707_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v_getLevel_708_);
lean_ctor_set(v_reuseFailAlloc_725_, 5, v_congrInfo_709_);
lean_ctor_set(v_reuseFailAlloc_725_, 6, v_defEqI_710_);
lean_ctor_set(v_reuseFailAlloc_725_, 7, v_extensions_711_);
lean_ctor_set(v_reuseFailAlloc_725_, 8, v_issues_712_);
lean_ctor_set(v_reuseFailAlloc_725_, 9, v_canon_713_);
lean_ctor_set(v_reuseFailAlloc_725_, 10, v___x_719_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, sizeof(void*)*11, v_debug_715_);
v___x_721_ = v_reuseFailAlloc_725_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = lean_st_ref_set(v_a_701_, v___x_721_);
v___x_723_ = lean_box(0);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___redArg___boxed(lean_object* v_type_727_, lean_object* v_inst_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Meta_Sym_registerInstance___redArg(v_type_727_, v_inst_728_, v_a_729_);
lean_dec(v_a_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance(lean_object* v_type_732_, lean_object* v_inst_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Meta_Sym_registerInstance___redArg(v_type_732_, v_inst_733_, v_a_735_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___boxed(lean_object* v_type_742_, lean_object* v_inst_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Meta_Sym_registerInstance(v_type_742_, v_inst_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0(lean_object* v_00_u03b2_752_, lean_object* v_x_753_, lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(v_x_753_, v_x_754_, v_x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0(lean_object* v_00_u03b2_757_, lean_object* v_x_758_, size_t v_x_759_, size_t v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_758_, v_x_759_, v_x_760_, v_x_761_, v_x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___boxed(lean_object* v_00_u03b2_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
size_t v_x_937__boxed_770_; size_t v_x_938__boxed_771_; lean_object* v_res_772_; 
v_x_937__boxed_770_ = lean_unbox_usize(v_x_766_);
lean_dec(v_x_766_);
v_x_938__boxed_771_ = lean_unbox_usize(v_x_767_);
lean_dec(v_x_767_);
v_res_772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0(v_00_u03b2_764_, v_x_765_, v_x_937__boxed_770_, v_x_938__boxed_771_, v_x_768_, v_x_769_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_773_, lean_object* v_n_774_, lean_object* v_k_775_, lean_object* v_v_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(v_n_774_, v_k_775_, v_v_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_778_, size_t v_depth_779_, lean_object* v_keys_780_, lean_object* v_vals_781_, lean_object* v_heq_782_, lean_object* v_i_783_, lean_object* v_entries_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_depth_779_, v_keys_780_, v_vals_781_, v_i_783_, v_entries_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_786_, lean_object* v_depth_787_, lean_object* v_keys_788_, lean_object* v_vals_789_, lean_object* v_heq_790_, lean_object* v_i_791_, lean_object* v_entries_792_){
_start:
{
size_t v_depth_boxed_793_; lean_object* v_res_794_; 
v_depth_boxed_793_ = lean_unbox_usize(v_depth_787_);
lean_dec(v_depth_787_);
v_res_794_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2(v_00_u03b2_786_, v_depth_boxed_793_, v_keys_788_, v_vals_789_, v_heq_790_, v_i_791_, v_entries_792_);
lean_dec_ref(v_vals_789_);
lean_dec_ref(v_keys_788_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_x_796_, v_x_797_, v_x_798_, v_x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_801_, lean_object* v_vals_802_, lean_object* v_i_803_, lean_object* v_k_804_){
_start:
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = lean_array_get_size(v_keys_801_);
v___x_806_ = lean_nat_dec_lt(v_i_803_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
lean_dec(v_i_803_);
v___x_807_ = lean_box(0);
return v___x_807_;
}
else
{
lean_object* v_k_x27_808_; uint8_t v___x_809_; 
v_k_x27_808_ = lean_array_fget_borrowed(v_keys_801_, v_i_803_);
v___x_809_ = lean_expr_eqv(v_k_804_, v_k_x27_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_unsigned_to_nat(1u);
v___x_811_ = lean_nat_add(v_i_803_, v___x_810_);
lean_dec(v_i_803_);
v_i_803_ = v___x_811_;
goto _start;
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_array_fget_borrowed(v_vals_802_, v_i_803_);
lean_dec(v_i_803_);
lean_inc(v___x_813_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_815_, lean_object* v_vals_816_, lean_object* v_i_817_, lean_object* v_k_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_keys_815_, v_vals_816_, v_i_817_, v_k_818_);
lean_dec_ref(v_k_818_);
lean_dec_ref(v_vals_816_);
lean_dec_ref(v_keys_815_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(lean_object* v_x_820_, size_t v_x_821_, lean_object* v_x_822_){
_start:
{
if (lean_obj_tag(v_x_820_) == 0)
{
lean_object* v_es_823_; lean_object* v___x_824_; size_t v___x_825_; size_t v___x_826_; lean_object* v_j_827_; lean_object* v___x_828_; 
v_es_823_ = lean_ctor_get(v_x_820_, 0);
v___x_824_ = lean_box(2);
v___x_825_ = ((size_t)31ULL);
v___x_826_ = lean_usize_land(v_x_821_, v___x_825_);
v_j_827_ = lean_usize_to_nat(v___x_826_);
v___x_828_ = lean_array_get_borrowed(v___x_824_, v_es_823_, v_j_827_);
lean_dec(v_j_827_);
switch(lean_obj_tag(v___x_828_))
{
case 0:
{
lean_object* v_key_829_; lean_object* v_val_830_; uint8_t v___x_831_; 
v_key_829_ = lean_ctor_get(v___x_828_, 0);
v_val_830_ = lean_ctor_get(v___x_828_, 1);
v___x_831_ = lean_expr_eqv(v_x_822_, v_key_829_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
v___x_832_ = lean_box(0);
return v___x_832_;
}
else
{
lean_object* v___x_833_; 
lean_inc(v_val_830_);
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v_val_830_);
return v___x_833_;
}
}
case 1:
{
lean_object* v_node_834_; size_t v___x_835_; size_t v___x_836_; 
v_node_834_ = lean_ctor_get(v___x_828_, 0);
v___x_835_ = ((size_t)5ULL);
v___x_836_ = lean_usize_shift_right(v_x_821_, v___x_835_);
v_x_820_ = v_node_834_;
v_x_821_ = v___x_836_;
goto _start;
}
default: 
{
lean_object* v___x_838_; 
v___x_838_ = lean_box(0);
return v___x_838_;
}
}
}
else
{
lean_object* v_ks_839_; lean_object* v_vs_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_ks_839_ = lean_ctor_get(v_x_820_, 0);
v_vs_840_ = lean_ctor_get(v_x_820_, 1);
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_ks_839_, v_vs_840_, v___x_841_, v_x_822_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
size_t v_x_748__boxed_846_; lean_object* v_res_847_; 
v_x_748__boxed_846_ = lean_unbox_usize(v_x_844_);
lean_dec(v_x_844_);
v_res_847_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_843_, v_x_748__boxed_846_, v_x_845_);
lean_dec_ref(v_x_845_);
lean_dec_ref(v_x_843_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
uint64_t v___x_850_; size_t v___x_851_; lean_object* v___x_852_; 
v___x_850_ = l_Lean_Expr_hash(v_x_849_);
v___x_851_ = lean_uint64_to_usize(v___x_850_);
v___x_852_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_848_, v___x_851_, v_x_849_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg___boxed(lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_x_853_, v_x_854_);
lean_dec_ref(v_x_854_);
lean_dec_ref(v_x_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object* v_type_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_863_; lean_object* v_instanceOverrides_864_; lean_object* v___x_865_; 
v___x_863_ = lean_st_ref_get(v_a_857_);
v_instanceOverrides_864_ = lean_ctor_get(v___x_863_, 10);
lean_inc_ref(v_instanceOverrides_864_);
lean_dec(v___x_863_);
v___x_865_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_instanceOverrides_864_, v_type_856_);
lean_dec_ref(v_instanceOverrides_864_);
if (lean_obj_tag(v___x_865_) == 1)
{
lean_object* v___x_866_; 
lean_dec_ref(v_type_856_);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
else
{
lean_object* v___x_867_; 
lean_dec(v___x_865_);
v___x_867_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_856_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg___boxed(lean_object* v_type_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f(lean_object* v_type_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_876_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___boxed(lean_object* v_type_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Meta_Sym_synthInstance_x3f(v_type_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0(lean_object* v_00_u03b2_894_, lean_object* v_x_895_, lean_object* v_x_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_x_895_, v_x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___boxed(lean_object* v_00_u03b2_898_, lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0(v_00_u03b2_898_, v_x_899_, v_x_900_);
lean_dec_ref(v_x_900_);
lean_dec_ref(v_x_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0(lean_object* v_00_u03b2_902_, lean_object* v_x_903_, size_t v_x_904_, lean_object* v_x_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_903_, v_x_904_, v_x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_907_, lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
size_t v_x_832__boxed_911_; lean_object* v_res_912_; 
v_x_832__boxed_911_ = lean_unbox_usize(v_x_909_);
lean_dec(v_x_909_);
v_res_912_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0(v_00_u03b2_907_, v_x_908_, v_x_832__boxed_911_, v_x_910_);
lean_dec_ref(v_x_910_);
lean_dec_ref(v_x_908_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_913_, lean_object* v_keys_914_, lean_object* v_vals_915_, lean_object* v_heq_916_, lean_object* v_i_917_, lean_object* v_k_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_keys_914_, v_vals_915_, v_i_917_, v_k_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_920_, lean_object* v_keys_921_, lean_object* v_vals_922_, lean_object* v_heq_923_, lean_object* v_i_924_, lean_object* v_k_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1(v_00_u03b2_920_, v_keys_921_, v_vals_922_, v_heq_923_, v_i_924_, v_k_925_);
lean_dec_ref(v_k_925_);
lean_dec_ref(v_vals_922_);
lean_dec_ref(v_keys_921_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(lean_object* v_msgData_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; lean_object* v_env_934_; lean_object* v___x_935_; lean_object* v_mctx_936_; lean_object* v_lctx_937_; lean_object* v_options_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_933_ = lean_st_ref_get(v___y_931_);
v_env_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc_ref(v_env_934_);
lean_dec(v___x_933_);
v___x_935_ = lean_st_ref_get(v___y_929_);
v_mctx_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc_ref(v_mctx_936_);
lean_dec(v___x_935_);
v_lctx_937_ = lean_ctor_get(v___y_928_, 2);
v_options_938_ = lean_ctor_get(v___y_930_, 2);
lean_inc_ref(v_options_938_);
lean_inc_ref(v_lctx_937_);
v___x_939_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_939_, 0, v_env_934_);
lean_ctor_set(v___x_939_, 1, v_mctx_936_);
lean_ctor_set(v___x_939_, 2, v_lctx_937_);
lean_ctor_set(v___x_939_, 3, v_options_938_);
v___x_940_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v_msgData_927_);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0___boxed(lean_object* v_msgData_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(v_msgData_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(lean_object* v_msg_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_ref_955_; lean_object* v___x_956_; lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_965_; 
v_ref_955_ = lean_ctor_get(v___y_952_, 5);
v___x_956_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(v_msg_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_965_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
lean_inc(v_ref_955_);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v_ref_955_);
lean_ctor_set(v___x_961_, 1, v_a_957_);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 1);
lean_ctor_set(v___x_959_, 0, v___x_961_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg___boxed(lean_object* v_msg_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v_msg_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_972_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_synthInstance___closed__1(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l_Lean_Meta_Sym_synthInstance___closed__0));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance(lean_object* v_type_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_984_; 
lean_inc_ref(v_type_976_);
v___x_984_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_976_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_997_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_997_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_997_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_997_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
if (lean_obj_tag(v_a_985_) == 1)
{
lean_object* v_val_989_; lean_object* v___x_991_; 
lean_dec_ref(v_type_976_);
v_val_989_ = lean_ctor_get(v_a_985_, 0);
lean_inc(v_val_989_);
lean_dec_ref_known(v_a_985_, 1);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v_val_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_val_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
lean_del_object(v___x_987_);
lean_dec(v_a_985_);
v___x_993_ = lean_obj_once(&l_Lean_Meta_Sym_synthInstance___closed__1, &l_Lean_Meta_Sym_synthInstance___closed__1_once, _init_l_Lean_Meta_Sym_synthInstance___closed__1);
v___x_994_ = l_Lean_indentExpr(v_type_976_);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v___x_995_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
return v___x_996_;
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref(v_type_976_);
v_a_998_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_984_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_984_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance___boxed(lean_object* v_type_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Meta_Sym_synthInstance(v_type_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0(lean_object* v_00_u03b1_1015_, lean_object* v_msg_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v_msg_1016_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___boxed(lean_object* v_00_u03b1_1025_, lean_object* v_msg_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0(v_00_u03b1_1025_, v_msg_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(lean_object* v_x_1035_, lean_object* v_type_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1055_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1055_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1055_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
if (lean_obj_tag(v_a_1044_) == 1)
{
lean_object* v_val_1048_; lean_object* v___x_1049_; 
lean_del_object(v___x_1046_);
v_val_1048_ = lean_ctor_get(v_a_1044_, 0);
lean_inc(v_val_1048_);
lean_dec_ref_known(v_a_1044_, 1);
v___x_1049_ = l_Lean_Meta_isExprDefEq(v_x_1035_, v_val_1048_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
return v___x_1049_;
}
else
{
uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
lean_dec(v_a_1044_);
lean_dec_ref(v_x_1035_);
v___x_1050_ = 0;
v___x_1051_ = lean_box(v___x_1050_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1051_);
v___x_1053_ = v___x_1046_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v_x_1035_);
v_a_1056_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1043_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1043_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg___boxed(lean_object* v_x_1064_, lean_object* v_type_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_x_1064_, v_type_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign(lean_object* v_x_1073_, lean_object* v_type_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_x_1073_, v_type_1074_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___boxed(lean_object* v_x_1083_, lean_object* v_type_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Meta_Sym_synthInstanceAndAssign(v_x_1083_, v_type_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
return v_res_1092_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_OrderLevel(uint8_t builtin);
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
res = runtime_initialize_Lean_OrderLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier = _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier();
lean_mark_persistent(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier);
l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier = _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier();
lean_mark_persistent(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier);
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
lean_object* initialize_Lean_OrderLevel(uint8_t builtin);
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
res = initialize_Lean_OrderLevel(builtin);
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
