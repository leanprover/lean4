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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__7_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instOfNatNat"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(217, 8, 172, 44, 179, 254, 147, 95)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__10;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 253, 199, 38, 151, 242, 146)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__13;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__15_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTNat"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(141, 27, 201, 217, 48, 203, 85, 203)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decLt"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(70, 116, 195, 81, 41, 93, 3, 179)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__19 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__20;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLENat"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__21 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(211, 47, 64, 46, 87, 101, 57, 105)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__22 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__22_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decLe"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__23 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__23_value),LEAN_SCALAR_PTR_LITERAL(222, 181, 165, 207, 140, 26, 31, 233)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__24 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__24_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__25;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__26 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__71_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__26_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__27_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__28 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__76_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__29_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLEInt"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__30_value),LEAN_SCALAR_PTR_LITERAL(190, 143, 147, 243, 104, 145, 221, 241)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__32_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__23_value),LEAN_SCALAR_PTR_LITERAL(64, 211, 213, 110, 61, 40, 149, 63)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__32 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__32_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__33;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTInt"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__34 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__34_value),LEAN_SCALAR_PTR_LITERAL(174, 212, 102, 196, 69, 170, 149, 126)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__36_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(168, 105, 33, 134, 172, 206, 181, 195)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__36 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__36_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__37;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instDecidableEqNat"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__38 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__38_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__38_value),LEAN_SCALAR_PTR_LITERAL(14, 141, 250, 24, 208, 103, 93, 195)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__39 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__39_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__40;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "instDecidableEq"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__41 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__41_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__42_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__41_value),LEAN_SCALAR_PTR_LITERAL(3, 193, 133, 18, 69, 57, 20, 76)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__42 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__42_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__43;
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
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__10(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_box(0);
v___x_638_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__9));
v___x_639_ = l_Lean_mkConst(v___x_638_, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__13(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = lean_box(0);
v___x_644_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__12));
v___x_645_ = l_Lean_mkConst(v___x_644_, v___x_643_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__20(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_box(0);
v___x_657_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__19));
v___x_658_ = l_Lean_mkConst(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__25(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_box(0);
v___x_667_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__24));
v___x_668_ = l_Lean_mkConst(v___x_667_, v___x_666_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__33(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = lean_box(0);
v___x_685_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__32));
v___x_686_ = l_Lean_mkConst(v___x_685_, v___x_684_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__37(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_box(0);
v___x_695_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__36));
v___x_696_ = l_Lean_mkConst(v___x_695_, v___x_694_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__40(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_box(0);
v___x_701_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__39));
v___x_702_ = l_Lean_mkConst(v___x_701_, v___x_700_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__43(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_box(0);
v___x_708_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__42));
v___x_709_ = l_Lean_mkConst(v___x_708_, v___x_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f(lean_object* v_type_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts;
v___x_712_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v___x_711_, v_type_710_);
if (lean_obj_tag(v___x_712_) == 1)
{
return v___x_712_;
}
else
{
lean_object* v___x_713_; uint8_t v___x_714_; 
lean_dec(v___x_712_);
v___x_713_ = l_Lean_Expr_cleanupAnnotations(v_type_710_);
v___x_714_ = l_Lean_Expr_isApp(v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
lean_dec_ref(v___x_713_);
v___x_715_ = lean_box(0);
return v___x_715_;
}
else
{
lean_object* v_arg_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_arg_716_ = lean_ctor_get(v___x_713_, 1);
lean_inc_ref(v_arg_716_);
v___x_717_ = l_Lean_Expr_appFnCleanup___redArg(v___x_713_);
lean_dec_ref(v___x_713_);
v___x_718_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__1));
v___x_719_ = l_Lean_Expr_isConstOf(v___x_717_, v___x_718_);
if (v___x_719_ == 0)
{
uint8_t v___x_720_; 
v___x_720_ = l_Lean_Expr_isApp(v___x_717_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
lean_dec_ref(v___x_717_);
lean_dec_ref(v_arg_716_);
v___x_721_ = lean_box(0);
return v___x_721_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = l_Lean_Expr_appFnCleanup___redArg(v___x_717_);
v___x_723_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__3));
v___x_724_ = l_Lean_Expr_isConstOf(v___x_722_, v___x_723_);
lean_dec_ref(v___x_722_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
lean_dec_ref(v___x_717_);
lean_dec_ref(v_arg_716_);
v___x_725_ = lean_box(0);
return v___x_725_;
}
else
{
lean_object* v_arg_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_arg_726_ = lean_ctor_get(v___x_717_, 1);
lean_inc_ref(v_arg_726_);
lean_dec_ref(v___x_717_);
v___x_727_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5));
v___x_728_ = l_Lean_Expr_isConstOf(v_arg_726_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__7));
v___x_730_ = l_Lean_Expr_isConstOf(v_arg_726_, v___x_729_);
lean_dec_ref(v_arg_726_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
lean_dec_ref(v_arg_716_);
v___x_731_ = lean_box(0);
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__10, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__10_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__10);
v___x_733_ = l_Lean_Expr_app___override(v___x_732_, v_arg_716_);
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec_ref(v_arg_726_);
v___x_735_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__13, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__13_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__13);
v___x_736_ = l_Lean_Expr_app___override(v___x_735_, v_arg_716_);
v___x_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
}
}
else
{
lean_object* v___x_738_; uint8_t v___x_739_; 
lean_dec_ref(v___x_717_);
v___x_738_ = l_Lean_Expr_cleanupAnnotations(v_arg_716_);
lean_dec_ref(v_arg_716_);
v___x_739_ = l_Lean_Expr_isApp(v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec_ref(v___x_738_);
v___x_740_ = lean_box(0);
return v___x_740_;
}
else
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = l_Lean_Expr_appFnCleanup___redArg(v___x_738_);
v___x_742_ = l_Lean_Expr_isApp(v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
v___x_743_ = lean_box(0);
return v___x_743_;
}
else
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = l_Lean_Expr_appFnCleanup___redArg(v___x_741_);
v___x_745_ = l_Lean_Expr_isApp(v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
v___x_746_ = lean_box(0);
return v___x_746_;
}
else
{
lean_object* v_arg_747_; lean_object* v_arg_748_; lean_object* v_arg_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_arg_747_ = lean_ctor_get(v___x_738_, 1);
lean_inc_ref(v_arg_747_);
lean_dec_ref(v___x_738_);
v_arg_748_ = lean_ctor_get(v___x_741_, 1);
lean_inc_ref(v_arg_748_);
lean_dec_ref(v___x_741_);
v_arg_749_ = lean_ctor_get(v___x_744_, 1);
lean_inc_ref(v_arg_749_);
v___x_750_ = l_Lean_Expr_appFnCleanup___redArg(v___x_744_);
lean_dec_ref(v___x_744_);
v___x_751_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__15));
v___x_752_ = l_Lean_Expr_isConstOf(v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
uint8_t v___x_753_; 
v___x_753_ = l_Lean_Expr_isApp(v___x_750_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v_arg_749_);
lean_dec_ref(v_arg_748_);
lean_dec_ref(v_arg_747_);
v___x_754_ = lean_box(0);
return v___x_754_;
}
else
{
lean_object* v_arg_755_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_arg_755_ = lean_ctor_get(v___x_750_, 1);
lean_inc_ref(v_arg_755_);
v___x_776_ = l_Lean_Expr_appFnCleanup___redArg(v___x_750_);
lean_dec_ref(v___x_750_);
v___x_777_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__27));
v___x_778_ = l_Lean_Expr_isConstOf(v___x_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__29));
v___x_780_ = l_Lean_Expr_isConstOf(v___x_776_, v___x_779_);
lean_dec_ref(v___x_776_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_dec_ref(v_arg_755_);
lean_dec_ref(v_arg_749_);
lean_dec_ref(v_arg_748_);
lean_dec_ref(v_arg_747_);
v___x_781_ = lean_box(0);
return v___x_781_;
}
else
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5));
v___x_783_ = l_Lean_Expr_isConstOf(v_arg_755_, v___x_782_);
if (v___x_783_ == 0)
{
goto v___jp_766_;
}
else
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31));
v___x_785_ = l_Lean_Expr_isConstOf(v_arg_749_, v___x_784_);
if (v___x_785_ == 0)
{
goto v___jp_766_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref(v_arg_755_);
lean_dec_ref(v_arg_749_);
v___x_786_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__33, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__33_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__33);
v___x_787_ = l_Lean_mkAppB(v___x_786_, v_arg_748_, v_arg_747_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
}
}
}
else
{
lean_object* v___x_789_; uint8_t v___x_790_; 
lean_dec_ref(v___x_776_);
v___x_789_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5));
v___x_790_ = l_Lean_Expr_isConstOf(v_arg_755_, v___x_789_);
if (v___x_790_ == 0)
{
goto v___jp_756_;
}
else
{
lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35));
v___x_792_ = l_Lean_Expr_isConstOf(v_arg_749_, v___x_791_);
if (v___x_792_ == 0)
{
goto v___jp_756_;
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec_ref(v_arg_755_);
lean_dec_ref(v_arg_749_);
v___x_793_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__37, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__37_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__37);
v___x_794_ = l_Lean_mkAppB(v___x_793_, v_arg_748_, v_arg_747_);
v___x_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
}
v___jp_756_:
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__7));
v___x_758_ = l_Lean_Expr_isConstOf(v_arg_755_, v___x_757_);
lean_dec_ref(v_arg_755_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
lean_dec_ref(v_arg_749_);
lean_dec_ref(v_arg_748_);
lean_dec_ref(v_arg_747_);
v___x_759_ = lean_box(0);
return v___x_759_;
}
else
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17));
v___x_761_ = l_Lean_Expr_isConstOf(v_arg_749_, v___x_760_);
lean_dec_ref(v_arg_749_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; 
lean_dec_ref(v_arg_748_);
lean_dec_ref(v_arg_747_);
v___x_762_ = lean_box(0);
return v___x_762_;
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__20, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__20_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__20);
v___x_764_ = l_Lean_mkAppB(v___x_763_, v_arg_748_, v_arg_747_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
}
v___jp_766_:
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__7));
v___x_768_ = l_Lean_Expr_isConstOf(v_arg_755_, v___x_767_);
lean_dec_ref(v_arg_755_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_dec_ref(v_arg_749_);
lean_dec_ref(v_arg_748_);
lean_dec_ref(v_arg_747_);
v___x_769_ = lean_box(0);
return v___x_769_;
}
else
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__22));
v___x_771_ = l_Lean_Expr_isConstOf(v_arg_749_, v___x_770_);
lean_dec_ref(v_arg_749_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_dec_ref(v_arg_748_);
lean_dec_ref(v_arg_747_);
v___x_772_ = lean_box(0);
return v___x_772_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__25, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__25_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__25);
v___x_774_ = l_Lean_mkAppB(v___x_773_, v_arg_748_, v_arg_747_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
}
}
}
else
{
lean_object* v___x_796_; uint8_t v___x_797_; 
lean_dec_ref(v___x_750_);
v___x_796_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5));
v___x_797_ = l_Lean_Expr_isConstOf(v_arg_749_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__7));
v___x_799_ = l_Lean_Expr_isConstOf(v_arg_749_, v___x_798_);
lean_dec_ref(v_arg_749_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; 
lean_dec_ref(v_arg_748_);
lean_dec_ref(v_arg_747_);
v___x_800_ = lean_box(0);
return v___x_800_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__40, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__40_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__40);
v___x_802_ = l_Lean_mkAppB(v___x_801_, v_arg_748_, v_arg_747_);
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref(v_arg_749_);
v___x_804_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__43, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__43_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__43);
v___x_805_ = l_Lean_mkAppB(v___x_804_, v_arg_748_, v_arg_747_);
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___boxed(lean_object* v_type_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Meta_Sym_getBuiltinInstance_x3f(v_type_807_);
lean_dec_ref(v_type_807_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0(lean_object* v_00_u03b2_809_, lean_object* v_m_810_, lean_object* v_a_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v_m_810_, v_a_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___boxed(lean_object* v_00_u03b2_813_, lean_object* v_m_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0(v_00_u03b2_813_, v_m_814_, v_a_815_);
lean_dec_ref(v_a_815_);
lean_dec_ref(v_m_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0(lean_object* v_00_u03b2_817_, lean_object* v_a_818_, lean_object* v_x_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(v_a_818_, v_x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_821_, lean_object* v_a_822_, lean_object* v_x_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0(v_00_u03b2_821_, v_a_822_, v_x_823_);
lean_dec(v_x_823_);
lean_dec_ref(v_a_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(lean_object* v_category_825_, lean_object* v_opts_826_, lean_object* v_act_827_, lean_object* v_decl_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
v___x_834_ = lean_apply_4(v_act_827_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
v___x_835_ = l_Lean_profileitIOUnsafe___redArg(v_category_825_, v_opts_826_, v___x_834_, v_decl_828_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg___boxed(lean_object* v_category_836_, lean_object* v_opts_837_, lean_object* v_act_838_, lean_object* v_decl_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v_category_836_, v_opts_837_, v_act_838_, v_decl_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v_opts_837_);
lean_dec_ref(v_category_836_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(lean_object* v_00_u03b1_846_, lean_object* v_category_847_, lean_object* v_opts_848_, lean_object* v_act_849_, lean_object* v_decl_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v_category_847_, v_opts_848_, v_act_849_, v_decl_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___boxed(lean_object* v_00_u03b1_857_, lean_object* v_category_858_, lean_object* v_opts_859_, lean_object* v_act_860_, lean_object* v_decl_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(v_00_u03b1_857_, v_category_858_, v_opts_859_, v_act_860_, v_decl_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v_opts_859_);
lean_dec_ref(v_category_858_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(lean_object* v___x_868_, lean_object* v_type_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
if (lean_obj_tag(v___x_868_) == 1)
{
lean_object* v___x_875_; 
lean_dec_ref(v_type_869_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_868_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec(v___x_868_);
v___x_876_ = l_Lean_Meta_isDefEqStuckExceptionId;
v___x_877_ = lean_box(0);
v___x_878_ = l_Lean_Meta_synthInstanceCore_x3f(v_type_869_, v___x_877_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_878_) == 0)
{
return v___x_878_;
}
else
{
lean_object* v_a_879_; uint8_t v___x_880_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v___x_880_ = l_Lean_Exception_isInterrupt(v_a_879_);
if (v___x_880_ == 0)
{
uint8_t v___x_881_; 
lean_inc(v_a_879_);
v___x_881_ = l_Lean_Exception_isRuntime(v_a_879_);
if (v___x_881_ == 0)
{
if (lean_obj_tag(v_a_879_) == 0)
{
return v___x_878_;
}
else
{
lean_object* v_id_882_; uint8_t v___x_883_; 
v_id_882_ = lean_ctor_get(v_a_879_, 0);
v___x_883_ = l_Lean_instBEqInternalExceptionId_beq(v___x_876_, v_id_882_);
if (v___x_883_ == 0)
{
return v___x_878_;
}
else
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v___x_878_, 0);
lean_dec(v_unused_891_);
v___x_885_ = v___x_878_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_dec(v___x_878_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set_tag(v___x_885_, 0);
lean_ctor_set(v___x_885_, 0, v___x_877_);
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_877_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
else
{
return v___x_878_;
}
}
else
{
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed(lean_object* v___x_892_, lean_object* v_type_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(v___x_892_, v_type_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object* v_type_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___y_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_907_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_904_);
v___x_908_ = ((lean_object*)(l_Lean_Meta_Sym_synthInstanceMeta_x3f___closed__0));
v___x_909_ = l_Lean_Meta_Sym_getBuiltinInstance_x3f(v_type_901_);
lean_inc_ref(v_type_901_);
v___y_910_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___y_910_, 0, v___x_909_);
lean_closure_set(v___y_910_, 1, v_type_901_);
v___x_911_ = l_Lean_Expr_getAppFn(v_type_901_);
lean_dec_ref(v_type_901_);
v___x_912_ = l_Lean_Expr_constName_x3f(v___x_911_);
lean_dec_ref(v___x_911_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_box(0);
v___x_914_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v___x_908_, v___x_907_, v___y_910_, v___x_913_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
lean_dec_ref(v___x_907_);
return v___x_914_;
}
else
{
lean_object* v_val_915_; lean_object* v___x_916_; 
v_val_915_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_val_915_);
lean_dec_ref_known(v___x_912_, 1);
v___x_916_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v___x_908_, v___x_907_, v___y_910_, v_val_915_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
lean_dec_ref(v___x_907_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___boxed(lean_object* v_type_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_924_, lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
lean_object* v_ks_928_; lean_object* v_vs_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_953_; 
v_ks_928_ = lean_ctor_get(v_x_924_, 0);
v_vs_929_ = lean_ctor_get(v_x_924_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_x_924_);
if (v_isSharedCheck_953_ == 0)
{
v___x_931_ = v_x_924_;
v_isShared_932_ = v_isSharedCheck_953_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_vs_929_);
lean_inc(v_ks_928_);
lean_dec(v_x_924_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_953_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_array_get_size(v_ks_928_);
v___x_934_ = lean_nat_dec_lt(v_x_925_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
lean_dec(v_x_925_);
v___x_935_ = lean_array_push(v_ks_928_, v_x_926_);
v___x_936_ = lean_array_push(v_vs_929_, v_x_927_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_936_);
lean_ctor_set(v___x_931_, 0, v___x_935_);
v___x_938_ = v___x_931_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
lean_object* v_k_x27_940_; uint8_t v___x_941_; 
v_k_x27_940_ = lean_array_fget_borrowed(v_ks_928_, v_x_925_);
v___x_941_ = lean_expr_eqv(v_x_926_, v_k_x27_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_943_; 
if (v_isShared_932_ == 0)
{
v___x_943_ = v___x_931_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_ks_928_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_vs_929_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_unsigned_to_nat(1u);
v___x_945_ = lean_nat_add(v_x_925_, v___x_944_);
lean_dec(v_x_925_);
v_x_924_ = v___x_943_;
v_x_925_ = v___x_945_;
goto _start;
}
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_948_ = lean_array_fset(v_ks_928_, v_x_925_, v_x_926_);
v___x_949_ = lean_array_fset(v_vs_929_, v_x_925_, v_x_927_);
lean_dec(v_x_925_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_949_);
lean_ctor_set(v___x_931_, 0, v___x_948_);
v___x_951_ = v___x_931_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_n_954_, lean_object* v_k_955_, lean_object* v_v_956_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_954_, v___x_957_, v_k_955_, v_v_956_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(lean_object* v_x_960_, size_t v_x_961_, size_t v_x_962_, lean_object* v_x_963_, lean_object* v_x_964_){
_start:
{
if (lean_obj_tag(v_x_960_) == 0)
{
lean_object* v_es_965_; size_t v___x_966_; size_t v___x_967_; lean_object* v_j_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v_es_965_ = lean_ctor_get(v_x_960_, 0);
v___x_966_ = ((size_t)31ULL);
v___x_967_ = lean_usize_land(v_x_961_, v___x_966_);
v_j_968_ = lean_usize_to_nat(v___x_967_);
v___x_969_ = lean_array_get_size(v_es_965_);
v___x_970_ = lean_nat_dec_lt(v_j_968_, v___x_969_);
if (v___x_970_ == 0)
{
lean_dec(v_j_968_);
lean_dec(v_x_964_);
lean_dec_ref(v_x_963_);
return v_x_960_;
}
else
{
lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1009_; 
lean_inc_ref(v_es_965_);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_x_960_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_x_960_, 0);
lean_dec(v_unused_1010_);
v___x_972_ = v_x_960_;
v_isShared_973_ = v_isSharedCheck_1009_;
goto v_resetjp_971_;
}
else
{
lean_dec(v_x_960_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1009_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v_v_974_; lean_object* v___x_975_; lean_object* v_xs_x27_976_; lean_object* v___y_978_; 
v_v_974_ = lean_array_fget(v_es_965_, v_j_968_);
v___x_975_ = lean_box(0);
v_xs_x27_976_ = lean_array_fset(v_es_965_, v_j_968_, v___x_975_);
switch(lean_obj_tag(v_v_974_))
{
case 0:
{
lean_object* v_key_983_; lean_object* v_val_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_994_; 
v_key_983_ = lean_ctor_get(v_v_974_, 0);
v_val_984_ = lean_ctor_get(v_v_974_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_v_974_);
if (v_isSharedCheck_994_ == 0)
{
v___x_986_ = v_v_974_;
v_isShared_987_ = v_isSharedCheck_994_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_val_984_);
lean_inc(v_key_983_);
lean_dec(v_v_974_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_994_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
uint8_t v___x_988_; 
v___x_988_ = lean_expr_eqv(v_x_963_, v_key_983_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_del_object(v___x_986_);
v___x_989_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_983_, v_val_984_, v_x_963_, v_x_964_);
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
v___y_978_ = v___x_990_;
goto v___jp_977_;
}
else
{
lean_object* v___x_992_; 
lean_dec(v_val_984_);
lean_dec(v_key_983_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v_x_964_);
lean_ctor_set(v___x_986_, 0, v_x_963_);
v___x_992_ = v___x_986_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_x_963_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_x_964_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
v___y_978_ = v___x_992_;
goto v___jp_977_;
}
}
}
}
case 1:
{
lean_object* v_node_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1007_; 
v_node_995_ = lean_ctor_get(v_v_974_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_v_974_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_997_ = v_v_974_;
v_isShared_998_ = v_isSharedCheck_1007_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_node_995_);
lean_dec(v_v_974_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1007_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
size_t v___x_999_; size_t v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_999_ = ((size_t)5ULL);
v___x_1000_ = lean_usize_shift_right(v_x_961_, v___x_999_);
v___x_1001_ = ((size_t)1ULL);
v___x_1002_ = lean_usize_add(v_x_962_, v___x_1001_);
v___x_1003_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_node_995_, v___x_1000_, v___x_1002_, v_x_963_, v_x_964_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1003_);
v___x_1005_ = v___x_997_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
v___y_978_ = v___x_1005_;
goto v___jp_977_;
}
}
}
default: 
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v_x_963_);
lean_ctor_set(v___x_1008_, 1, v_x_964_);
v___y_978_ = v___x_1008_;
goto v___jp_977_;
}
}
v___jp_977_:
{
lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_979_ = lean_array_fset(v_xs_x27_976_, v_j_968_, v___y_978_);
lean_dec(v_j_968_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_979_);
v___x_981_ = v___x_972_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
else
{
lean_object* v_ks_1011_; lean_object* v_vs_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1030_; 
v_ks_1011_ = lean_ctor_get(v_x_960_, 0);
v_vs_1012_ = lean_ctor_get(v_x_960_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_x_960_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1014_ = v_x_960_;
v_isShared_1015_ = v_isSharedCheck_1030_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_vs_1012_);
lean_inc(v_ks_1011_);
lean_dec(v_x_960_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1030_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_ks_1011_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_vs_1012_);
v___x_1017_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v_newNode_1018_; size_t v___x_1019_; uint8_t v___x_1020_; 
v_newNode_1018_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(v___x_1017_, v_x_963_, v_x_964_);
v___x_1019_ = ((size_t)7ULL);
v___x_1020_ = lean_usize_dec_le(v___x_1019_, v_x_962_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1021_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1018_);
v___x_1022_ = lean_unsigned_to_nat(4u);
v___x_1023_ = lean_nat_dec_lt(v___x_1021_, v___x_1022_);
lean_dec(v___x_1021_);
if (v___x_1023_ == 0)
{
lean_object* v_ks_1024_; lean_object* v_vs_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_ks_1024_ = lean_ctor_get(v_newNode_1018_, 0);
lean_inc_ref(v_ks_1024_);
v_vs_1025_ = lean_ctor_get(v_newNode_1018_, 1);
lean_inc_ref(v_vs_1025_);
lean_dec_ref(v_newNode_1018_);
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0);
v___x_1028_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_x_962_, v_ks_1024_, v_vs_1025_, v___x_1026_, v___x_1027_);
lean_dec_ref(v_vs_1025_);
lean_dec_ref(v_ks_1024_);
return v___x_1028_;
}
else
{
return v_newNode_1018_;
}
}
else
{
return v_newNode_1018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(size_t v_depth_1031_, lean_object* v_keys_1032_, lean_object* v_vals_1033_, lean_object* v_i_1034_, lean_object* v_entries_1035_){
_start:
{
lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = lean_array_get_size(v_keys_1032_);
v___x_1037_ = lean_nat_dec_lt(v_i_1034_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_dec(v_i_1034_);
return v_entries_1035_;
}
else
{
lean_object* v_k_1038_; lean_object* v_v_1039_; uint64_t v___x_1040_; size_t v_h_1041_; size_t v___x_1042_; lean_object* v___x_1043_; size_t v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; size_t v_h_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_k_1038_ = lean_array_fget_borrowed(v_keys_1032_, v_i_1034_);
v_v_1039_ = lean_array_fget_borrowed(v_vals_1033_, v_i_1034_);
v___x_1040_ = l_Lean_Expr_hash(v_k_1038_);
v_h_1041_ = lean_uint64_to_usize(v___x_1040_);
v___x_1042_ = ((size_t)5ULL);
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = ((size_t)1ULL);
v___x_1045_ = lean_usize_sub(v_depth_1031_, v___x_1044_);
v___x_1046_ = lean_usize_mul(v___x_1042_, v___x_1045_);
v_h_1047_ = lean_usize_shift_right(v_h_1041_, v___x_1046_);
v___x_1048_ = lean_nat_add(v_i_1034_, v___x_1043_);
lean_dec(v_i_1034_);
lean_inc(v_v_1039_);
lean_inc(v_k_1038_);
v___x_1049_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_entries_1035_, v_h_1047_, v_depth_1031_, v_k_1038_, v_v_1039_);
v_i_1034_ = v___x_1048_;
v_entries_1035_ = v___x_1049_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1051_, lean_object* v_keys_1052_, lean_object* v_vals_1053_, lean_object* v_i_1054_, lean_object* v_entries_1055_){
_start:
{
size_t v_depth_boxed_1056_; lean_object* v_res_1057_; 
v_depth_boxed_1056_ = lean_unbox_usize(v_depth_1051_);
lean_dec(v_depth_1051_);
v_res_1057_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1056_, v_keys_1052_, v_vals_1053_, v_i_1054_, v_entries_1055_);
lean_dec_ref(v_vals_1053_);
lean_dec_ref(v_keys_1052_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___boxed(lean_object* v_x_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
size_t v_x_737__boxed_1063_; size_t v_x_738__boxed_1064_; lean_object* v_res_1065_; 
v_x_737__boxed_1063_ = lean_unbox_usize(v_x_1059_);
lean_dec(v_x_1059_);
v_x_738__boxed_1064_ = lean_unbox_usize(v_x_1060_);
lean_dec(v_x_1060_);
v_res_1065_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_1058_, v_x_737__boxed_1063_, v_x_738__boxed_1064_, v_x_1061_, v_x_1062_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(lean_object* v_x_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_){
_start:
{
uint64_t v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v___x_1069_ = l_Lean_Expr_hash(v_x_1067_);
v___x_1070_ = lean_uint64_to_usize(v___x_1069_);
v___x_1071_ = ((size_t)1ULL);
v___x_1072_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_1066_, v___x_1070_, v___x_1071_, v_x_1067_, v_x_1068_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object* v_type_1073_, lean_object* v_inst_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v___x_1077_; lean_object* v_share_1078_; lean_object* v_maxFVar_1079_; lean_object* v_proofInstInfo_1080_; lean_object* v_proofInstInfoFVar_1081_; lean_object* v_inferType_1082_; lean_object* v_getLevel_1083_; lean_object* v_congrInfo_1084_; lean_object* v_defEqI_1085_; lean_object* v_extensions_1086_; lean_object* v_issues_1087_; lean_object* v_canon_1088_; lean_object* v_instanceOverrides_1089_; uint8_t v_debug_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1101_; 
v___x_1077_ = lean_st_ref_take(v_a_1075_);
v_share_1078_ = lean_ctor_get(v___x_1077_, 0);
v_maxFVar_1079_ = lean_ctor_get(v___x_1077_, 1);
v_proofInstInfo_1080_ = lean_ctor_get(v___x_1077_, 2);
v_proofInstInfoFVar_1081_ = lean_ctor_get(v___x_1077_, 3);
v_inferType_1082_ = lean_ctor_get(v___x_1077_, 4);
v_getLevel_1083_ = lean_ctor_get(v___x_1077_, 5);
v_congrInfo_1084_ = lean_ctor_get(v___x_1077_, 6);
v_defEqI_1085_ = lean_ctor_get(v___x_1077_, 7);
v_extensions_1086_ = lean_ctor_get(v___x_1077_, 8);
v_issues_1087_ = lean_ctor_get(v___x_1077_, 9);
v_canon_1088_ = lean_ctor_get(v___x_1077_, 10);
v_instanceOverrides_1089_ = lean_ctor_get(v___x_1077_, 11);
v_debug_1090_ = lean_ctor_get_uint8(v___x_1077_, sizeof(void*)*12);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1092_ = v___x_1077_;
v_isShared_1093_ = v_isSharedCheck_1101_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_instanceOverrides_1089_);
lean_inc(v_canon_1088_);
lean_inc(v_issues_1087_);
lean_inc(v_extensions_1086_);
lean_inc(v_defEqI_1085_);
lean_inc(v_congrInfo_1084_);
lean_inc(v_getLevel_1083_);
lean_inc(v_inferType_1082_);
lean_inc(v_proofInstInfoFVar_1081_);
lean_inc(v_proofInstInfo_1080_);
lean_inc(v_maxFVar_1079_);
lean_inc(v_share_1078_);
lean_dec(v___x_1077_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1101_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1094_ = lean_box(0);
v___x_1095_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(v_instanceOverrides_1089_, v_type_1073_, v_inst_1074_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 11, v___x_1095_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_share_1078_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_maxFVar_1079_);
lean_ctor_set(v_reuseFailAlloc_1100_, 2, v_proofInstInfo_1080_);
lean_ctor_set(v_reuseFailAlloc_1100_, 3, v_proofInstInfoFVar_1081_);
lean_ctor_set(v_reuseFailAlloc_1100_, 4, v_inferType_1082_);
lean_ctor_set(v_reuseFailAlloc_1100_, 5, v_getLevel_1083_);
lean_ctor_set(v_reuseFailAlloc_1100_, 6, v_congrInfo_1084_);
lean_ctor_set(v_reuseFailAlloc_1100_, 7, v_defEqI_1085_);
lean_ctor_set(v_reuseFailAlloc_1100_, 8, v_extensions_1086_);
lean_ctor_set(v_reuseFailAlloc_1100_, 9, v_issues_1087_);
lean_ctor_set(v_reuseFailAlloc_1100_, 10, v_canon_1088_);
lean_ctor_set(v_reuseFailAlloc_1100_, 11, v___x_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1100_, sizeof(void*)*12, v_debug_1090_);
v___x_1097_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_st_ref_put(v_a_1075_, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1094_);
return v___x_1099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___redArg___boxed(lean_object* v_type_1102_, lean_object* v_inst_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_Meta_Sym_registerInstance___redArg(v_type_1102_, v_inst_1103_, v_a_1104_);
lean_dec(v_a_1104_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance(lean_object* v_type_1107_, lean_object* v_inst_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_Meta_Sym_registerInstance___redArg(v_type_1107_, v_inst_1108_, v_a_1110_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___boxed(lean_object* v_type_1117_, lean_object* v_inst_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Meta_Sym_registerInstance(v_type_1117_, v_inst_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0(lean_object* v_00_u03b2_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(v_x_1128_, v_x_1129_, v_x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0(lean_object* v_00_u03b2_1132_, lean_object* v_x_1133_, size_t v_x_1134_, size_t v_x_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_1133_, v_x_1134_, v_x_1135_, v_x_1136_, v_x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
size_t v_x_943__boxed_1145_; size_t v_x_944__boxed_1146_; lean_object* v_res_1147_; 
v_x_943__boxed_1145_ = lean_unbox_usize(v_x_1141_);
lean_dec(v_x_1141_);
v_x_944__boxed_1146_ = lean_unbox_usize(v_x_1142_);
lean_dec(v_x_1142_);
v_res_1147_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0(v_00_u03b2_1139_, v_x_1140_, v_x_943__boxed_1145_, v_x_944__boxed_1146_, v_x_1143_, v_x_1144_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1148_, lean_object* v_n_1149_, lean_object* v_k_1150_, lean_object* v_v_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(v_n_1149_, v_k_1150_, v_v_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1153_, size_t v_depth_1154_, lean_object* v_keys_1155_, lean_object* v_vals_1156_, lean_object* v_heq_1157_, lean_object* v_i_1158_, lean_object* v_entries_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_depth_1154_, v_keys_1155_, v_vals_1156_, v_i_1158_, v_entries_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1161_, lean_object* v_depth_1162_, lean_object* v_keys_1163_, lean_object* v_vals_1164_, lean_object* v_heq_1165_, lean_object* v_i_1166_, lean_object* v_entries_1167_){
_start:
{
size_t v_depth_boxed_1168_; lean_object* v_res_1169_; 
v_depth_boxed_1168_ = lean_unbox_usize(v_depth_1162_);
lean_dec(v_depth_1162_);
v_res_1169_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2(v_00_u03b2_1161_, v_depth_boxed_1168_, v_keys_1163_, v_vals_1164_, v_heq_1165_, v_i_1166_, v_entries_1167_);
lean_dec_ref(v_vals_1164_);
lean_dec_ref(v_keys_1163_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1171_, v_x_1172_, v_x_1173_, v_x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1176_, lean_object* v_vals_1177_, lean_object* v_i_1178_, lean_object* v_k_1179_){
_start:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = lean_array_get_size(v_keys_1176_);
v___x_1181_ = lean_nat_dec_lt(v_i_1178_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
lean_dec(v_i_1178_);
v___x_1182_ = lean_box(0);
return v___x_1182_;
}
else
{
lean_object* v_k_x27_1183_; uint8_t v___x_1184_; 
v_k_x27_1183_ = lean_array_fget_borrowed(v_keys_1176_, v_i_1178_);
v___x_1184_ = lean_expr_eqv(v_k_1179_, v_k_x27_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_unsigned_to_nat(1u);
v___x_1186_ = lean_nat_add(v_i_1178_, v___x_1185_);
lean_dec(v_i_1178_);
v_i_1178_ = v___x_1186_;
goto _start;
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_array_fget_borrowed(v_vals_1177_, v_i_1178_);
lean_dec(v_i_1178_);
lean_inc(v___x_1188_);
v___x_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1190_, lean_object* v_vals_1191_, lean_object* v_i_1192_, lean_object* v_k_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1190_, v_vals_1191_, v_i_1192_, v_k_1193_);
lean_dec_ref(v_k_1193_);
lean_dec_ref(v_vals_1191_);
lean_dec_ref(v_keys_1190_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(lean_object* v_x_1195_, size_t v_x_1196_, lean_object* v_x_1197_){
_start:
{
if (lean_obj_tag(v_x_1195_) == 0)
{
lean_object* v_es_1198_; lean_object* v___x_1199_; size_t v___x_1200_; size_t v___x_1201_; lean_object* v_j_1202_; lean_object* v___x_1203_; 
v_es_1198_ = lean_ctor_get(v_x_1195_, 0);
v___x_1199_ = lean_box(2);
v___x_1200_ = ((size_t)31ULL);
v___x_1201_ = lean_usize_land(v_x_1196_, v___x_1200_);
v_j_1202_ = lean_usize_to_nat(v___x_1201_);
v___x_1203_ = lean_array_get_borrowed(v___x_1199_, v_es_1198_, v_j_1202_);
lean_dec(v_j_1202_);
switch(lean_obj_tag(v___x_1203_))
{
case 0:
{
lean_object* v_key_1204_; lean_object* v_val_1205_; uint8_t v___x_1206_; 
v_key_1204_ = lean_ctor_get(v___x_1203_, 0);
v_val_1205_ = lean_ctor_get(v___x_1203_, 1);
v___x_1206_ = lean_expr_eqv(v_x_1197_, v_key_1204_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_box(0);
return v___x_1207_;
}
else
{
lean_object* v___x_1208_; 
lean_inc(v_val_1205_);
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_val_1205_);
return v___x_1208_;
}
}
case 1:
{
lean_object* v_node_1209_; size_t v___x_1210_; size_t v___x_1211_; 
v_node_1209_ = lean_ctor_get(v___x_1203_, 0);
v___x_1210_ = ((size_t)5ULL);
v___x_1211_ = lean_usize_shift_right(v_x_1196_, v___x_1210_);
v_x_1195_ = v_node_1209_;
v_x_1196_ = v___x_1211_;
goto _start;
}
default: 
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_box(0);
return v___x_1213_;
}
}
}
else
{
lean_object* v_ks_1214_; lean_object* v_vs_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_ks_1214_ = lean_ctor_get(v_x_1195_, 0);
v_vs_1215_ = lean_ctor_get(v_x_1195_, 1);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1214_, v_vs_1215_, v___x_1216_, v_x_1197_);
return v___x_1217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1218_, lean_object* v_x_1219_, lean_object* v_x_1220_){
_start:
{
size_t v_x_747__boxed_1221_; lean_object* v_res_1222_; 
v_x_747__boxed_1221_ = lean_unbox_usize(v_x_1219_);
lean_dec(v_x_1219_);
v_res_1222_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_1218_, v_x_747__boxed_1221_, v_x_1220_);
lean_dec_ref(v_x_1220_);
lean_dec_ref(v_x_1218_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(lean_object* v_x_1223_, lean_object* v_x_1224_){
_start:
{
uint64_t v___x_1225_; size_t v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = l_Lean_Expr_hash(v_x_1224_);
v___x_1226_ = lean_uint64_to_usize(v___x_1225_);
v___x_1227_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_1223_, v___x_1226_, v_x_1224_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg___boxed(lean_object* v_x_1228_, lean_object* v_x_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_x_1228_, v_x_1229_);
lean_dec_ref(v_x_1229_);
lean_dec_ref(v_x_1228_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object* v_type_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v___x_1238_; lean_object* v_instanceOverrides_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_st_ref_get(v_a_1232_);
v_instanceOverrides_1239_ = lean_ctor_get(v___x_1238_, 11);
lean_inc_ref(v_instanceOverrides_1239_);
lean_dec(v___x_1238_);
v___x_1240_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_instanceOverrides_1239_, v_type_1231_);
lean_dec_ref(v_instanceOverrides_1239_);
if (lean_obj_tag(v___x_1240_) == 1)
{
lean_object* v___x_1241_; 
lean_dec_ref(v_type_1231_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
else
{
lean_object* v___x_1242_; 
lean_dec(v___x_1240_);
v___x_1242_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_1231_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg___boxed(lean_object* v_type_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f(lean_object* v_type_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1251_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___boxed(lean_object* v_type_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Meta_Sym_synthInstance_x3f(v_type_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0(lean_object* v_00_u03b2_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_x_1270_, v_x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___boxed(lean_object* v_00_u03b2_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0(v_00_u03b2_1273_, v_x_1274_, v_x_1275_);
lean_dec_ref(v_x_1275_);
lean_dec_ref(v_x_1274_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1277_, lean_object* v_x_1278_, size_t v_x_1279_, lean_object* v_x_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_1278_, v_x_1279_, v_x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_){
_start:
{
size_t v_x_831__boxed_1286_; lean_object* v_res_1287_; 
v_x_831__boxed_1286_ = lean_unbox_usize(v_x_1284_);
lean_dec(v_x_1284_);
v_res_1287_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0(v_00_u03b2_1282_, v_x_1283_, v_x_831__boxed_1286_, v_x_1285_);
lean_dec_ref(v_x_1285_);
lean_dec_ref(v_x_1283_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1288_, lean_object* v_keys_1289_, lean_object* v_vals_1290_, lean_object* v_heq_1291_, lean_object* v_i_1292_, lean_object* v_k_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1289_, v_vals_1290_, v_i_1292_, v_k_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1295_, lean_object* v_keys_1296_, lean_object* v_vals_1297_, lean_object* v_heq_1298_, lean_object* v_i_1299_, lean_object* v_k_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1295_, v_keys_1296_, v_vals_1297_, v_heq_1298_, v_i_1299_, v_k_1300_);
lean_dec_ref(v_k_1300_);
lean_dec_ref(v_vals_1297_);
lean_dec_ref(v_keys_1296_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(lean_object* v_msgData_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; lean_object* v_env_1309_; uint8_t v___x_1310_; lean_object* v_env_1311_; lean_object* v___x_1312_; lean_object* v_toCold_1313_; lean_object* v_mctx_1314_; lean_object* v_lctx_1315_; lean_object* v_options_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1308_ = lean_st_ref_get(v___y_1306_);
v_env_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc_ref(v_env_1309_);
lean_dec(v___x_1308_);
v___x_1310_ = 0;
v_env_1311_ = l_Lean_Environment_setRecordingDeps(v_env_1309_, v___x_1310_);
v___x_1312_ = lean_st_ref_get(v___y_1304_);
v_toCold_1313_ = lean_ctor_get(v___y_1305_, 0);
v_mctx_1314_ = lean_ctor_get(v___x_1312_, 0);
lean_inc_ref(v_mctx_1314_);
lean_dec(v___x_1312_);
v_lctx_1315_ = lean_ctor_get(v___y_1303_, 2);
v_options_1316_ = lean_ctor_get(v_toCold_1313_, 2);
lean_inc_ref(v_options_1316_);
lean_inc_ref(v_lctx_1315_);
v___x_1317_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1317_, 0, v_env_1311_);
lean_ctor_set(v___x_1317_, 1, v_mctx_1314_);
lean_ctor_set(v___x_1317_, 2, v_lctx_1315_);
lean_ctor_set(v___x_1317_, 3, v_options_1316_);
v___x_1318_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set(v___x_1318_, 1, v_msgData_1302_);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0___boxed(lean_object* v_msgData_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(v_msgData_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(lean_object* v_msg_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v_ref_1333_; lean_object* v___x_1334_; lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1343_; 
v_ref_1333_ = lean_ctor_get(v___y_1330_, 2);
v___x_1334_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(v_msg_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
lean_inc(v_ref_1333_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_ref_1333_);
lean_ctor_set(v___x_1339_, 1, v_a_1335_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set_tag(v___x_1337_, 1);
lean_ctor_set(v___x_1337_, 0, v___x_1339_);
v___x_1341_ = v___x_1337_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg___boxed(lean_object* v_msg_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v_msg_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1350_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_synthInstance___closed__1(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = ((lean_object*)(l_Lean_Meta_Sym_synthInstance___closed__0));
v___x_1353_ = l_Lean_stringToMessageData(v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance(lean_object* v_type_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v___x_1362_; 
lean_inc_ref(v_type_1354_);
v___x_1362_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1354_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1375_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1375_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1375_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
if (lean_obj_tag(v_a_1363_) == 1)
{
lean_object* v_val_1367_; lean_object* v___x_1369_; 
lean_dec_ref(v_type_1354_);
v_val_1367_ = lean_ctor_get(v_a_1363_, 0);
lean_inc(v_val_1367_);
lean_dec_ref_known(v_a_1363_, 1);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v_val_1367_);
v___x_1369_ = v___x_1365_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_val_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_del_object(v___x_1365_);
lean_dec(v_a_1363_);
v___x_1371_ = lean_obj_once(&l_Lean_Meta_Sym_synthInstance___closed__1, &l_Lean_Meta_Sym_synthInstance___closed__1_once, _init_l_Lean_Meta_Sym_synthInstance___closed__1);
v___x_1372_ = l_Lean_indentExpr(v_type_1354_);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v___x_1373_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_);
return v___x_1374_;
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec_ref(v_type_1354_);
v_a_1376_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1362_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1362_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance___boxed(lean_object* v_type_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Meta_Sym_synthInstance(v_type_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0(lean_object* v_00_u03b1_1393_, lean_object* v_msg_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v_msg_1394_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___boxed(lean_object* v_00_u03b1_1403_, lean_object* v_msg_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0(v_00_u03b1_1403_, v_msg_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(lean_object* v_x_1413_, lean_object* v_type_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1433_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1433_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1433_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
if (lean_obj_tag(v_a_1422_) == 1)
{
lean_object* v_val_1426_; lean_object* v___x_1427_; 
lean_del_object(v___x_1424_);
v_val_1426_ = lean_ctor_get(v_a_1422_, 0);
lean_inc(v_val_1426_);
lean_dec_ref_known(v_a_1422_, 1);
v___x_1427_ = l_Lean_Meta_isExprDefEq(v_x_1413_, v_val_1426_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
return v___x_1427_;
}
else
{
uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
lean_dec(v_a_1422_);
lean_dec_ref(v_x_1413_);
v___x_1428_ = 0;
v___x_1429_ = lean_box(v___x_1428_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1429_);
v___x_1431_ = v___x_1424_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec_ref(v_x_1413_);
v_a_1434_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1421_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1421_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg___boxed(lean_object* v_x_1442_, lean_object* v_type_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_x_1442_, v_type_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign(lean_object* v_x_1451_, lean_object* v_type_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_x_1451_, v_type_1452_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___boxed(lean_object* v_x_1461_, lean_object* v_type_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Meta_Sym_synthInstanceAndAssign(v_x_1461_, v_type_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
return v_res_1470_;
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
