// Lean compiler output
// Module: Lean.Meta.Sym.SynthInstance
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.SynthInstance import Init.Grind.Ring import Init.Grind.Ordered.Ring import Init.GrindInstances import Init.Grind.Ordered.Int import Init.Data.Int.Package
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
extern lean_object* l_Lean_Int_mkInstLE;
extern lean_object* l_Lean_Int_mkInstLT;
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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isDefEqStuckExceptionId;
lean_object* l_Lean_Meta_synthInstanceCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__0;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "instCommRingInt"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 31, 43, 123, 13, 223, 116, 234)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__5;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__6_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__7_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__11;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__12_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__13_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__16;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toCommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__6_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__17_value),LEAN_SCALAR_PTR_LITERAL(134, 95, 181, 253, 18, 104, 213, 131)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__19;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__20 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "toNatModule"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__21 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__20_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__21_value),LEAN_SCALAR_PTR_LITERAL(156, 107, 255, 119, 73, 35, 26, 237)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__22 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__23 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__23_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__13_value),LEAN_SCALAR_PTR_LITERAL(134, 3, 13, 60, 96, 160, 201, 59)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__24 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__24_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__25;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__26;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__27;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__28;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "instLinearOrderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__29 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__29_value),LEAN_SCALAR_PTR_LITERAL(131, 14, 207, 248, 19, 164, 92, 69)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__30 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__30_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__31;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LinearOrderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__33 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__33_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "toLinearPreorderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__34 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__34_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__35_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__33_value),LEAN_SCALAR_PTR_LITERAL(234, 23, 176, 82, 70, 91, 79, 141)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__35_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__34_value),LEAN_SCALAR_PTR_LITERAL(49, 11, 127, 82, 11, 218, 43, 122)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__35 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__35_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__36;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__37;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "PreorderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__38 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__38_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toIsPreorder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__39 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__39_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__40_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__38_value),LEAN_SCALAR_PTR_LITERAL(213, 46, 53, 169, 1, 182, 53, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__40_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__39_value),LEAN_SCALAR_PTR_LITERAL(102, 251, 239, 168, 167, 218, 99, 248)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__40 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__40_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "LinearPreorderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__41 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__41_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "toPreorderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__42 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__42_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__43_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__41_value),LEAN_SCALAR_PTR_LITERAL(225, 122, 95, 75, 156, 33, 23, 202)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__43_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__42_value),LEAN_SCALAR_PTR_LITERAL(220, 190, 227, 44, 91, 141, 117, 87)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__43 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__43_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__44;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__45;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__46;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__47;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__48;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__49;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instCommSemiringNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__50 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__50_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__51_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__51_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__50_value),LEAN_SCALAR_PTR_LITERAL(40, 222, 188, 237, 59, 115, 167, 190)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__51 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__51_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__52;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__54;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__55;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__56;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__57;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__59;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instIsPreorderNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__60 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__60_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__61_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__61_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__60_value),LEAN_SCALAR_PTR_LITERAL(82, 153, 165, 139, 213, 168, 248, 23)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__61 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__61_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__62;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instIsLinearOrder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__63 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__63_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__64_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__63_value),LEAN_SCALAR_PTR_LITERAL(65, 94, 2, 50, 92, 94, 216, 236)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__64 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__64_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__65;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__66 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__66_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__66_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__67 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__67_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__69;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDvd"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__70 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__70_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__71_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__70_value),LEAN_SCALAR_PTR_LITERAL(154, 210, 229, 77, 176, 177, 112, 145)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__71 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__71_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__72;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__73;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__74;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__75_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__75_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__6_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__75 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__75_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__77;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__78;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__79_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__79_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__12_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__79 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__79_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__80;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__81_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__81;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__82_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__82_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__23_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__82 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__82_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__83;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__84;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__85_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__85_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__85_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__20_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__85 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__85_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__86;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__87;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__88;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__89_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__89;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__90_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__90;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__91_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__91;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__92_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__92;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "IsLinearOrder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__93 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__93_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__94_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__93_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__94 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__94_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__96_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__96;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__97_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__97;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__98_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__98;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LawfulOrderLT"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__99 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__99_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__100_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__99_value),LEAN_SCALAR_PTR_LITERAL(125, 54, 67, 105, 183, 31, 31, 114)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__100 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__100_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__101;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__102_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__102;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__103_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__103;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__104_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__104;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "instLawfulOrderLTNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__105 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__105_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__106_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__106_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__106_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__106_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__105_value),LEAN_SCALAR_PTR_LITERAL(67, 147, 221, 102, 44, 68, 100, 197)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__106 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__106_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__107_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__107;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__108;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__109_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__109;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OrderedRing"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__110 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__110_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__111_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__111_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__111_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__110_value),LEAN_SCALAR_PTR_LITERAL(245, 123, 155, 51, 122, 17, 247, 247)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__111 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__111_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__112_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__112;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__113_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__113;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instOrderedRingNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__114 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__114_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__115_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__115_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__115_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__115_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__114_value),LEAN_SCALAR_PTR_LITERAL(151, 152, 80, 183, 84, 69, 75, 40)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__115 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__115_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__116_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__116;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__117_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__117;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__118_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__118;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__119 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__119_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__119_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__120 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__120_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__121_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__121;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__122 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__122_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__122_value),LEAN_SCALAR_PTR_LITERAL(164, 225, 253, 29, 29, 200, 99, 105)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__123 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__123_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__124_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__124;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__125_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__125;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__126_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__126;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Max"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__127 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__127_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__127_value),LEAN_SCALAR_PTR_LITERAL(169, 95, 226, 81, 206, 208, 89, 76)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__128 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__128_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__129_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__129;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instMax"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__130 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__130_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__131_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__131_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__130_value),LEAN_SCALAR_PTR_LITERAL(98, 227, 45, 92, 47, 209, 226, 196)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__131 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__131_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__132_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__132;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__133_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__133;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__134_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__134;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__135_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__135;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__136_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__136;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__137_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__137;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__138_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__138;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__139_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__139;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NatModule"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__140 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__140_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__141_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__141_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__141_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__141_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__140_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 171, 186, 15, 174, 251, 179)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__141 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__141_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__142_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__142;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__143_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__143;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__144_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__144;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NoNatZeroDivisors"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__145 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__145_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__146_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__146_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__146_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__146_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__145_value),LEAN_SCALAR_PTR_LITERAL(78, 29, 6, 12, 7, 77, 98, 78)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__146 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__146_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__147_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__147;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__148_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__148;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "instNoNatZeroDivisorsNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__149 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__149_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__150_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__150_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__150_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__150_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__149_value),LEAN_SCALAR_PTR_LITERAL(80, 62, 83, 18, 35, 229, 169, 162)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__150 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__150_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__151_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__151;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__152_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__152;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__153_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__153;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "IsPreorder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__154 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__154_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__155_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__155_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__154_value),LEAN_SCALAR_PTR_LITERAL(184, 213, 76, 156, 147, 68, 250, 139)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__155 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__155_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__156_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__156;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__157_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__157;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__158_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__158;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "IsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__159 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__159_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__160_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__160_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__159_value),LEAN_SCALAR_PTR_LITERAL(196, 84, 36, 174, 137, 182, 135, 55)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__160 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__160_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__161_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__161;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "toIsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__162 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__162_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__163_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__163_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__163_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__93_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__163_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__162_value),LEAN_SCALAR_PTR_LITERAL(83, 108, 214, 71, 226, 119, 72, 107)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__163 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__163_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__164_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__164;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__165_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__165;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__166_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__166;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__167_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__167;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__168_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__168;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "IsLinearPreorder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__169 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__169_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__170_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__170_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__169_value),LEAN_SCALAR_PTR_LITERAL(149, 98, 195, 196, 59, 47, 77, 198)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__170 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__170_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__171_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__171;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "toIsLinearPreorder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__172 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__172_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__173_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__173_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__173_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__93_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__173_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__173_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__172_value),LEAN_SCALAR_PTR_LITERAL(222, 35, 97, 11, 70, 227, 118, 244)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__173 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__173_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__174_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__174;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__175_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__175;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__176_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__176;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__177_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__177;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__178_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__178;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__179_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__179;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__180_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__180;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__181_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__181;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__182_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__182 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__182_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__183_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__183_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__183_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__183_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__182_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__183 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__183_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__184_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__184;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__185_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__185;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__186_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__186;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__187_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__187;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__188_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__188;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__189_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__189;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__190_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__190;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__191_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__191;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__192 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__192_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__193_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__193_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__193_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__193_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__193_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__192_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__193 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__193_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instAddNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__194 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__194_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__194_value),LEAN_SCALAR_PTR_LITERAL(228, 164, 175, 25, 228, 165, 175, 183)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__195 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__195_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__196_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__196;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__197_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__197;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__198_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__198;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__199_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "instAddRightCancelNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__199 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__199_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__200_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__200_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__200_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__200_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__200_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__199_value),LEAN_SCALAR_PTR_LITERAL(61, 59, 84, 219, 165, 123, 148, 70)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__200 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__200_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__201_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__201;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__202_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__202;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__203_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__203;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__204_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__204;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__205_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__205;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__206_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__206;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__207_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__207;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__209_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__209;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__210_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__210 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__210_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__211_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__210_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__211 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__211_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__212_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__212;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__213_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__213;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__214_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__214;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__215_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__215;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__216_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__216_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__216_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__130_value),LEAN_SCALAR_PTR_LITERAL(172, 71, 86, 64, 121, 239, 29, 46)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__216 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__216_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__217_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__217;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__218_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__218;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__219_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__219;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__220_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__220;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__221_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__221_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__221_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__70_value),LEAN_SCALAR_PTR_LITERAL(164, 20, 243, 72, 185, 226, 91, 120)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__221 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__221_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__222_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__222;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__223_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__223;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__224_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__224;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__225_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__225;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__226_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__226;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__227_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__227;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__228_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__228;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__229_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__229;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__230_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__230;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__231_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__231;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__232_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__232;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__233_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__233;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__235_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__235;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__236_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__236_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__236_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__41_value),LEAN_SCALAR_PTR_LITERAL(225, 122, 95, 75, 156, 33, 23, 202)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__236_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__236_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__172_value),LEAN_SCALAR_PTR_LITERAL(136, 249, 219, 90, 192, 97, 192, 138)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__236 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__236_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__237_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__237;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__238_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__238;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__239_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__239;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__240_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__240;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__241_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "instIsLinearOrderInt"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__241 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__241_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__242_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__242_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__242_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__242_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__242_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__241_value),LEAN_SCALAR_PTR_LITERAL(131, 250, 55, 79, 188, 53, 20, 57)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__242 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__242_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__243_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__243;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__244_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__244;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__245_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__245;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__246_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__246;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__247_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__247;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__248_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "instLawfulOrderLTInt"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__248 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__248_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__249_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__249_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__249_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__249_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__249_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__248_value),LEAN_SCALAR_PTR_LITERAL(15, 49, 64, 177, 151, 67, 90, 197)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__249 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__249_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__250_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__250;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__251_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__251;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__252_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__252;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__253_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__253;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__254_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__254;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__255_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instOrderedRingInt"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__255 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__255_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__256_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__256_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__256_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__256_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__256_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__255_value),LEAN_SCALAR_PTR_LITERAL(39, 57, 139, 49, 47, 134, 165, 10)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__256 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__256_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__257_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__257;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__258_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__258;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__259_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__259;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__260_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__260;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__261_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__261;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__262_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__262;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__263_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__263;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__264_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__264;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__265_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__265;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__266_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__266;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__267_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__267;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__268_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__268;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__269_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__269;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__270_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__270;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__271_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "instNoNatZeroDivisorsInt"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__271 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__271_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__272_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__272_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__272_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__272_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__272_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__271_value),LEAN_SCALAR_PTR_LITERAL(78, 244, 183, 128, 140, 77, 95, 233)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__272 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__272_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__273_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__273;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__274_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__274;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__275_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__275;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__276_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__276;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__277_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__277;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__278_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__278;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__279_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__279;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__280_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "PartialOrderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__280 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__280_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__281_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__281_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__281_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__280_value),LEAN_SCALAR_PTR_LITERAL(161, 83, 12, 138, 219, 25, 15, 147)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__281_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__281_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__162_value),LEAN_SCALAR_PTR_LITERAL(189, 36, 219, 76, 135, 177, 227, 44)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__281 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__281_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__282_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "toPartialOrderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__282 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__282_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__283_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__283_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__283_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__33_value),LEAN_SCALAR_PTR_LITERAL(234, 23, 176, 82, 70, 91, 79, 141)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__283_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__283_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__282_value),LEAN_SCALAR_PTR_LITERAL(104, 50, 28, 184, 150, 106, 140, 110)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__283 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__283_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__284_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__284;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__285_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__285;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__286_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__286;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__287_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__287;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__288_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__288;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__289_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__289;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__290_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__290;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__291_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__291;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__292_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__292;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__293_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__293;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__294_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__294;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__295_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__295;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__296_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__296;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__297_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__297;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__298_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__298;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__299_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__299;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__300_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__300;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__301_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__301;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__302_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__302;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__303_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__303;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__304_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__304;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__305_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__305;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__306_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__306;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__307_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__307;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__308_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__308;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__309_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__309;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__310_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__310;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "PowIdentity"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 166, 196, 137, 32, 118, 33, 172)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IsCharP"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 211, 245, 119, 67, 24, 212, 73)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instIsCharPNatOfNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(184, 168, 68, 32, 159, 176, 186, 43)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__7;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "instIsCharPIntOfNatNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(81, 208, 198, 28, 57, 9, 161, 62)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(lean_object* v_z_825_, lean_object* v_n_826_, lean_object* v_args_827_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = l_Lean_mkConst(v_n_826_, v_z_825_);
v___x_829_ = l_Lean_mkAppN(v___x_828_, v_args_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0___boxed(lean_object* v_z_830_, lean_object* v_n_831_, lean_object* v_args_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_830_, v_n_831_, v_args_832_);
lean_dec_ref(v_args_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0_spec__0___redArg(lean_object* v_as_x27_834_, lean_object* v_b_835_){
_start:
{
if (lean_obj_tag(v_as_x27_834_) == 0)
{
return v_b_835_;
}
else
{
lean_object* v_head_836_; lean_object* v_tail_837_; lean_object* v_fst_838_; lean_object* v_snd_839_; lean_object* v_r_840_; 
v_head_836_ = lean_ctor_get(v_as_x27_834_, 0);
v_tail_837_ = lean_ctor_get(v_as_x27_834_, 1);
v_fst_838_ = lean_ctor_get(v_head_836_, 0);
v_snd_839_ = lean_ctor_get(v_head_836_, 1);
lean_inc(v_snd_839_);
lean_inc(v_fst_838_);
v_r_840_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0___redArg(v_b_835_, v_fst_838_, v_snd_839_);
v_as_x27_834_ = v_tail_837_;
v_b_835_ = v_r_840_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0_spec__0___redArg___boxed(lean_object* v_as_x27_842_, lean_object* v_b_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0_spec__0___redArg(v_as_x27_842_, v_b_843_);
lean_dec(v_as_x27_842_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0(lean_object* v_m_845_, lean_object* v_l_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0_spec__0___redArg(v_l_846_, v_m_845_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0___boxed(lean_object* v_m_848_, lean_object* v_l_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0(v_m_848_, v_l_849_);
lean_dec(v_l_849_);
return v_res_850_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__0(void){
_start:
{
lean_object* v___x_851_; lean_object* v_prop_852_; 
v___x_851_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35);
v_prop_852_ = l_Lean_mkSort(v___x_851_);
return v_prop_852_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__5(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v_crI_862_; 
v___x_860_ = lean_box(0);
v___x_861_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__4));
v_crI_862_ = l_Lean_mkConst(v___x_861_, v___x_860_);
return v_crI_862_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9(void){
_start:
{
lean_object* v_int_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_int_870_ = l_Lean_Int_mkType;
v___x_871_ = lean_unsigned_to_nat(2u);
v___x_872_ = lean_mk_empty_array_with_capacity(v___x_871_);
v___x_873_ = lean_array_push(v___x_872_, v_int_870_);
return v___x_873_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__10(void){
_start:
{
lean_object* v_crI_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_crI_874_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__5, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__5_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__5);
v___x_875_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9);
v___x_876_ = lean_array_push(v___x_875_, v_crI_874_);
return v___x_876_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__11(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v_z_879_; lean_object* v_ringI_880_; 
v___x_877_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__10, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__10_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__10);
v___x_878_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__8));
v_z_879_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v_ringI_880_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_879_, v___x_878_, v___x_877_);
return v_ringI_880_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__15(void){
_start:
{
lean_object* v_ringI_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_ringI_888_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__11, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__11_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__11);
v___x_889_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9);
v___x_890_ = lean_array_push(v___x_889_, v_ringI_888_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__16(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_z_893_; lean_object* v_srI_894_; 
v___x_891_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__15, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__15_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__15);
v___x_892_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__14));
v_z_893_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v_srI_894_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_893_, v___x_892_, v___x_891_);
return v_srI_894_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__19(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v_z_903_; lean_object* v_csI_904_; 
v___x_901_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__10, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__10_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__10);
v___x_902_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__18));
v_z_903_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v_csI_904_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_903_, v___x_902_, v___x_901_);
return v_csI_904_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__25(void){
_start:
{
lean_object* v_csI_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_csI_918_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__19, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__19_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__19);
v___x_919_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9);
v___x_920_ = lean_array_push(v___x_919_, v_csI_918_);
return v___x_920_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__26(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_z_923_; lean_object* v___x_924_; 
v___x_921_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__25, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__25_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__25);
v___x_922_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__24));
v_z_923_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_924_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_923_, v___x_922_, v___x_921_);
return v___x_924_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__27(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__26, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__26_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__26);
v___x_926_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9);
v___x_927_ = lean_array_push(v___x_926_, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__28(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_z_930_; lean_object* v_nmI_931_; 
v___x_928_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__27, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__27_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__27);
v___x_929_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__22));
v_z_930_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v_nmI_931_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_930_, v___x_929_, v___x_928_);
return v_nmI_931_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__31(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v_lopI_938_; 
v___x_936_ = lean_box(0);
v___x_937_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__30));
v_lopI_938_ = l_Lean_mkConst(v___x_937_, v___x_936_);
return v_lopI_938_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__36(void){
_start:
{
lean_object* v_lopI_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_lopI_946_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__31, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__31_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__31);
v___x_947_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9);
v___x_948_ = lean_array_push(v___x_947_, v_lopI_946_);
return v___x_948_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__37(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v_z_951_; lean_object* v_lppI_952_; 
v___x_949_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__36);
v___x_950_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__35));
v_z_951_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v_lppI_952_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_951_, v___x_950_, v___x_949_);
return v_lppI_952_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__44(void){
_start:
{
lean_object* v_lppI_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_lppI_965_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__37, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__37_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__37);
v___x_966_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9);
v___x_967_ = lean_array_push(v___x_966_, v_lppI_965_);
return v___x_967_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__45(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v_z_970_; lean_object* v___x_971_; 
v___x_968_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__44, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__44_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__44);
v___x_969_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__43));
v_z_970_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_971_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_970_, v___x_969_, v___x_968_);
return v___x_971_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__46(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__45, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__45_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__45);
v___x_973_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9);
v___x_974_ = lean_array_push(v___x_973_, v___x_972_);
return v___x_974_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__47(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_z_977_; lean_object* v_preI_978_; 
v___x_975_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__46, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__46_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__46);
v___x_976_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__40));
v_z_977_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v_preI_978_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_977_, v___x_976_, v___x_975_);
return v_preI_978_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__48(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_leI_981_; 
v___x_979_ = lean_box(0);
v___x_980_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31));
v_leI_981_ = l_Lean_mkConst(v___x_980_, v___x_979_);
return v_leI_981_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__49(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_ltI_984_; 
v___x_982_ = lean_box(0);
v___x_983_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35));
v_ltI_984_ = l_Lean_mkConst(v___x_983_, v___x_982_);
return v_ltI_984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__52(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v_csN_992_; 
v___x_990_ = lean_box(0);
v___x_991_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__51));
v_csN_992_ = l_Lean_mkConst(v___x_991_, v___x_990_);
return v_csN_992_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53(void){
_start:
{
lean_object* v_nat_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_nat_993_ = l_Lean_Nat_mkType;
v___x_994_ = lean_unsigned_to_nat(2u);
v___x_995_ = lean_mk_empty_array_with_capacity(v___x_994_);
v___x_996_ = lean_array_push(v___x_995_, v_nat_993_);
return v___x_996_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__54(void){
_start:
{
lean_object* v_csN_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_csN_997_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__52, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__52_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__52);
v___x_998_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53);
v___x_999_ = lean_array_push(v___x_998_, v_csN_997_);
return v___x_999_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__55(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_z_1002_; lean_object* v_srN_1003_; 
v___x_1000_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__54, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__54_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__54);
v___x_1001_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__24));
v_z_1002_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v_srN_1003_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1002_, v___x_1001_, v___x_1000_);
return v_srN_1003_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__56(void){
_start:
{
lean_object* v_srN_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_srN_1004_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__55, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__55_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__55);
v___x_1005_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53);
v___x_1006_ = lean_array_push(v___x_1005_, v_srN_1004_);
return v___x_1006_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__57(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_z_1009_; lean_object* v_nmN_1010_; 
v___x_1007_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__56, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__56_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__56);
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__22));
v_z_1009_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v_nmN_1010_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1009_, v___x_1008_, v___x_1007_);
return v_nmN_1010_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_leN_1013_; 
v___x_1011_ = lean_box(0);
v___x_1012_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__22));
v_leN_1013_ = l_Lean_mkConst(v___x_1012_, v___x_1011_);
return v_leN_1013_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__59(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v_ltN_1016_; 
v___x_1014_ = lean_box(0);
v___x_1015_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17));
v_ltN_1016_ = l_Lean_mkConst(v___x_1015_, v___x_1014_);
return v_ltN_1016_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__62(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_preN_1024_; 
v___x_1022_ = lean_box(0);
v___x_1023_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__61));
v_preN_1024_ = l_Lean_mkConst(v___x_1023_, v___x_1022_);
return v_preN_1024_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__65(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_linN_1031_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__64));
v_linN_1031_ = l_Lean_mkConst(v___x_1030_, v___x_1029_);
return v_linN_1031_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68(void){
_start:
{
lean_object* v_nat_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v_nat_1035_ = l_Lean_Nat_mkType;
v___x_1036_ = lean_unsigned_to_nat(1u);
v___x_1037_ = lean_mk_empty_array_with_capacity(v___x_1036_);
v___x_1038_ = lean_array_push(v___x_1037_, v_nat_1035_);
return v___x_1038_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__69(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v_z_1041_; lean_object* v___x_1042_; 
v___x_1039_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68);
v___x_1040_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__67));
v_z_1041_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1042_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1041_, v___x_1040_, v___x_1039_);
return v___x_1042_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__72(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = lean_box(0);
v___x_1048_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__71));
v___x_1049_ = l_Lean_mkConst(v___x_1048_, v___x_1047_);
return v___x_1049_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__73(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__72, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__72_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__72);
v___x_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__74(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__73, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__73_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__73);
v___x_1053_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__69, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__69_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__69);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___x_1052_);
return v___x_1054_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76(void){
_start:
{
lean_object* v_prop_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_prop_1059_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__0, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__0_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__0);
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1061_ = lean_mk_empty_array_with_capacity(v___x_1060_);
v___x_1062_ = lean_array_push(v___x_1061_, v_prop_1059_);
return v___x_1062_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__77(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_z_1065_; lean_object* v___x_1066_; 
v___x_1063_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76);
v___x_1064_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__75));
v_z_1065_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1066_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1065_, v___x_1064_, v___x_1063_);
return v___x_1066_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__78(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__77, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__77_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__77);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1067_);
return v___x_1069_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__80(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_z_1076_; lean_object* v___x_1077_; 
v___x_1074_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76);
v___x_1075_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__79));
v_z_1076_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1077_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1076_, v___x_1075_, v___x_1074_);
return v___x_1077_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__81(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__80, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__80_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__80);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v___x_1078_);
return v___x_1080_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__83(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v_z_1087_; lean_object* v___x_1088_; 
v___x_1085_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76);
v___x_1086_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__82));
v_z_1087_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1088_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1087_, v___x_1086_, v___x_1085_);
return v___x_1088_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__84(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__83, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__83_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__83);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v___x_1089_);
return v___x_1091_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__86(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v_z_1098_; lean_object* v___x_1099_; 
v___x_1096_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__76);
v___x_1097_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__85));
v_z_1098_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1099_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1098_, v___x_1097_, v___x_1096_);
return v___x_1099_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__87(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__86, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__86_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__86);
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v___x_1100_);
return v___x_1102_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__88(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__87, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__87_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__87);
v___x_1105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v___x_1103_);
return v___x_1105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__89(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__88, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__88_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__88);
v___x_1107_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__84, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__84_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__84);
v___x_1108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v___x_1106_);
return v___x_1108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__90(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__89, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__89_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__89);
v___x_1110_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__81, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__81_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__81);
v___x_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v___x_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__91(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__90, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__90_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__90);
v___x_1113_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__78, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__78_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__78);
v___x_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v___x_1112_);
return v___x_1114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__92(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v_x_1117_; 
v___x_1115_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__91, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__91_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__91);
v___x_1116_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__74, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__74_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__74);
v_x_1117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1117_, 0, v___x_1116_);
lean_ctor_set(v_x_1117_, 1, v___x_1115_);
return v_x_1117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95(void){
_start:
{
lean_object* v_leN_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_leN_1122_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58);
v___x_1123_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53);
v___x_1124_ = lean_array_push(v___x_1123_, v_leN_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__96(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_z_1127_; lean_object* v___x_1128_; 
v___x_1125_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95);
v___x_1126_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__94));
v_z_1127_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1128_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1127_, v___x_1126_, v___x_1125_);
return v___x_1128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__97(void){
_start:
{
lean_object* v_linN_1129_; lean_object* v___x_1130_; 
v_linN_1129_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__65, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__65_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__65);
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_linN_1129_);
return v___x_1130_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__98(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__97, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__97_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__97);
v___x_1132_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__96, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__96_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__96);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_ctor_set(v___x_1133_, 1, v___x_1131_);
return v___x_1133_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__101(void){
_start:
{
lean_object* v_nat_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_nat_1138_ = l_Lean_Nat_mkType;
v___x_1139_ = lean_unsigned_to_nat(3u);
v___x_1140_ = lean_mk_empty_array_with_capacity(v___x_1139_);
v___x_1141_ = lean_array_push(v___x_1140_, v_nat_1138_);
return v___x_1141_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__102(void){
_start:
{
lean_object* v_ltN_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_ltN_1142_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__59, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__59_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__59);
v___x_1143_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__101, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__101_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__101);
v___x_1144_ = lean_array_push(v___x_1143_, v_ltN_1142_);
return v___x_1144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__103(void){
_start:
{
lean_object* v_leN_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_leN_1145_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58);
v___x_1146_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__102, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__102_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__102);
v___x_1147_ = lean_array_push(v___x_1146_, v_leN_1145_);
return v___x_1147_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__104(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_z_1150_; lean_object* v___x_1151_; 
v___x_1148_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__103, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__103_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__103);
v___x_1149_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__100));
v_z_1150_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1151_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1150_, v___x_1149_, v___x_1148_);
return v___x_1151_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__107(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = lean_box(0);
v___x_1158_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__106));
v___x_1159_ = l_Lean_mkConst(v___x_1158_, v___x_1157_);
return v___x_1159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__108(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__107, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__107_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__107);
v___x_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__109(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__108, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__108_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__108);
v___x_1163_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__104, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__104_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__104);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v___x_1162_);
return v___x_1164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__112(void){
_start:
{
lean_object* v_preN_1170_; lean_object* v_ltN_1171_; lean_object* v_leN_1172_; lean_object* v_srN_1173_; lean_object* v_nat_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_preN_1170_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__62, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__62_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__62);
v_ltN_1171_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__59, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__59_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__59);
v_leN_1172_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58);
v_srN_1173_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__55, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__55_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__55);
v_nat_1174_ = l_Lean_Nat_mkType;
v___x_1175_ = lean_unsigned_to_nat(5u);
v___x_1176_ = lean_mk_empty_array_with_capacity(v___x_1175_);
v___x_1177_ = lean_array_push(v___x_1176_, v_nat_1174_);
v___x_1178_ = lean_array_push(v___x_1177_, v_srN_1173_);
v___x_1179_ = lean_array_push(v___x_1178_, v_leN_1172_);
v___x_1180_ = lean_array_push(v___x_1179_, v_ltN_1171_);
v___x_1181_ = lean_array_push(v___x_1180_, v_preN_1170_);
return v___x_1181_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__113(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_z_1184_; lean_object* v___x_1185_; 
v___x_1182_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__112, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__112_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__112);
v___x_1183_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__111));
v_z_1184_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1185_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1184_, v___x_1183_, v___x_1182_);
return v___x_1185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__116(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__115));
v___x_1193_ = l_Lean_mkConst(v___x_1192_, v___x_1191_);
return v___x_1193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__117(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__116, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__116_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__116);
v___x_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__118(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__117, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__117_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__117);
v___x_1197_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__113, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__113_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__113);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v___x_1196_);
return v___x_1198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__121(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_z_1204_; lean_object* v___x_1205_; 
v___x_1202_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68);
v___x_1203_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__120));
v_z_1204_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1205_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1204_, v___x_1203_, v___x_1202_);
return v___x_1205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__124(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_box(0);
v___x_1210_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__123));
v___x_1211_ = l_Lean_mkConst(v___x_1210_, v___x_1209_);
return v___x_1211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__125(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__124, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__124_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__124);
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__126(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__125, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__125_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__125);
v___x_1215_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__121, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__121_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__121);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1214_);
return v___x_1216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__129(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v_z_1222_; lean_object* v___x_1223_; 
v___x_1220_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68);
v___x_1221_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__128));
v_z_1222_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1223_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1222_, v___x_1221_, v___x_1220_);
return v___x_1223_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__132(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = lean_box(0);
v___x_1229_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__131));
v___x_1230_ = l_Lean_mkConst(v___x_1229_, v___x_1228_);
return v___x_1230_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__133(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__132, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__132_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__132);
v___x_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__134(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__133, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__133_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__133);
v___x_1234_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__129, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__129_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__129);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v___x_1233_);
return v___x_1235_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__135(void){
_start:
{
lean_object* v_x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_x_1236_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__92, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__92_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__92);
v___x_1237_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__134, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__134_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__134);
v___x_1238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v_x_1236_);
return v___x_1238_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__136(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__135, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__135_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__135);
v___x_1240_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__126, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__126_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__126);
v___x_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v___x_1239_);
return v___x_1241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__137(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__136, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__136_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__136);
v___x_1243_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__118, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__118_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__118);
v___x_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v___x_1242_);
return v___x_1244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__138(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__137, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__137_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__137);
v___x_1246_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__109, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__109_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__109);
v___x_1247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
lean_ctor_set(v___x_1247_, 1, v___x_1245_);
return v___x_1247_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__139(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v_x_1250_; 
v___x_1248_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__138, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__138_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__138);
v___x_1249_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__98, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__98_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__98);
v_x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1250_, 0, v___x_1249_);
lean_ctor_set(v_x_1250_, 1, v___x_1248_);
return v_x_1250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__142(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v_z_1258_; lean_object* v___x_1259_; 
v___x_1256_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68);
v___x_1257_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__141));
v_z_1258_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1259_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1258_, v___x_1257_, v___x_1256_);
return v___x_1259_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__143(void){
_start:
{
lean_object* v_nmN_1260_; lean_object* v___x_1261_; 
v_nmN_1260_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__57, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__57_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__57);
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_nmN_1260_);
return v___x_1261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__144(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__143, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__143_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__143);
v___x_1263_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__142, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__142_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__142);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v___x_1262_);
return v___x_1264_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__147(void){
_start:
{
lean_object* v_nmN_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_nmN_1270_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__57, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__57_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__57);
v___x_1271_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53);
v___x_1272_ = lean_array_push(v___x_1271_, v_nmN_1270_);
return v___x_1272_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__148(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v_z_1275_; lean_object* v___x_1276_; 
v___x_1273_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__147, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__147_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__147);
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__146));
v_z_1275_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1276_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1275_, v___x_1274_, v___x_1273_);
return v___x_1276_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__151(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_box(0);
v___x_1283_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__150));
v___x_1284_ = l_Lean_mkConst(v___x_1283_, v___x_1282_);
return v___x_1284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__152(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__151, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__151_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__151);
v___x_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__153(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__152, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__152_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__152);
v___x_1288_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__148, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__148_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__148);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v___x_1287_);
return v___x_1289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__156(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v_z_1296_; lean_object* v___x_1297_; 
v___x_1294_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95);
v___x_1295_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__155));
v_z_1296_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1297_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1296_, v___x_1295_, v___x_1294_);
return v___x_1297_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__157(void){
_start:
{
lean_object* v_preN_1298_; lean_object* v___x_1299_; 
v_preN_1298_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__62, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__62_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__62);
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_preN_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__158(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__157, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__157_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__157);
v___x_1301_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__156, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__156_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__156);
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1300_);
return v___x_1302_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__161(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v_z_1309_; lean_object* v___x_1310_; 
v___x_1307_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95);
v___x_1308_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__160));
v_z_1309_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1310_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1309_, v___x_1308_, v___x_1307_);
return v___x_1310_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__164(void){
_start:
{
lean_object* v_leN_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_leN_1316_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__58);
v___x_1317_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__101, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__101_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__101);
v___x_1318_ = lean_array_push(v___x_1317_, v_leN_1316_);
return v___x_1318_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__165(void){
_start:
{
lean_object* v_linN_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_linN_1319_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__65, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__65_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__65);
v___x_1320_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__164, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__164_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__164);
v___x_1321_ = lean_array_push(v___x_1320_, v_linN_1319_);
return v___x_1321_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__166(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v_z_1324_; lean_object* v___x_1325_; 
v___x_1322_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__165, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__165_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__165);
v___x_1323_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__163));
v_z_1324_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1325_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1324_, v___x_1323_, v___x_1322_);
return v___x_1325_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__167(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__166, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__166_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__166);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__168(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__167, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__167_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__167);
v___x_1329_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__161, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__161_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__161);
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v___x_1328_);
return v___x_1330_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__171(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v_z_1337_; lean_object* v___x_1338_; 
v___x_1335_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__95);
v___x_1336_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__170));
v_z_1337_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1338_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1337_, v___x_1336_, v___x_1335_);
return v___x_1338_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__174(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_z_1346_; lean_object* v___x_1347_; 
v___x_1344_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__165, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__165_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__165);
v___x_1345_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__173));
v_z_1346_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1347_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1346_, v___x_1345_, v___x_1344_);
return v___x_1347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__175(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__174, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__174_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__174);
v___x_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__176(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__175, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__175_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__175);
v___x_1351_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__171, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__171_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__171);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v___x_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__177(void){
_start:
{
lean_object* v_x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_x_1353_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__139, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__139_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__139);
v___x_1354_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__176, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__176_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__176);
v___x_1355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v_x_1353_);
return v___x_1355_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__178(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__177, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__177_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__177);
v___x_1357_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__168, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__168_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__168);
v___x_1358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___x_1356_);
return v___x_1358_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__179(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__178, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__178_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__178);
v___x_1360_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__158, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__158_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__158);
v___x_1361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v___x_1359_);
return v___x_1361_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__180(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__179, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__179_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__179);
v___x_1363_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__153, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__153_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__153);
v___x_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v___x_1362_);
return v___x_1364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__181(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v_x_1367_; 
v___x_1365_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__180, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__180_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__180);
v___x_1366_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__144, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__144_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__144);
v_x_1367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1367_, 0, v___x_1366_);
lean_ctor_set(v_x_1367_, 1, v___x_1365_);
return v_x_1367_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__184(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v_z_1375_; lean_object* v___x_1376_; 
v___x_1373_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68);
v___x_1374_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__183));
v_z_1375_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1376_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1375_, v___x_1374_, v___x_1373_);
return v___x_1376_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__185(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = lean_box(0);
v___x_1378_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__184, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__184_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__184);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
lean_ctor_set(v___x_1379_, 1, v___x_1377_);
return v___x_1379_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__186(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v_z_1382_; lean_object* v___x_1383_; 
v___x_1380_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68);
v___x_1381_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__82));
v_z_1382_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1383_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1382_, v___x_1381_, v___x_1380_);
return v___x_1383_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__187(void){
_start:
{
lean_object* v_csN_1384_; lean_object* v___x_1385_; 
v_csN_1384_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__52, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__52_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__52);
v___x_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1385_, 0, v_csN_1384_);
return v___x_1385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__188(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__187, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__187_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__187);
v___x_1387_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__186, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__186_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__186);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
lean_ctor_set(v___x_1388_, 1, v___x_1386_);
return v___x_1388_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__189(void){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v_z_1391_; lean_object* v___x_1392_; 
v___x_1389_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68);
v___x_1390_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__85));
v_z_1391_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1392_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1391_, v___x_1390_, v___x_1389_);
return v___x_1392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__190(void){
_start:
{
lean_object* v_srN_1393_; lean_object* v___x_1394_; 
v_srN_1393_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__55, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__55_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__55);
v___x_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1394_, 0, v_srN_1393_);
return v___x_1394_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__191(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__190, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__190_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__190);
v___x_1396_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__189, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__189_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__189);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v___x_1395_);
return v___x_1397_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__196(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = lean_box(0);
v___x_1407_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__195));
v___x_1408_ = l_Lean_mkConst(v___x_1407_, v___x_1406_);
return v___x_1408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__197(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__196, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__196_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__196);
v___x_1410_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__53);
v___x_1411_ = lean_array_push(v___x_1410_, v___x_1409_);
return v___x_1411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__198(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v_z_1414_; lean_object* v___x_1415_; 
v___x_1412_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__197, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__197_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__197);
v___x_1413_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__193));
v_z_1414_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1415_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1414_, v___x_1413_, v___x_1412_);
return v___x_1415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__201(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = lean_box(0);
v___x_1422_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__200));
v___x_1423_ = l_Lean_mkConst(v___x_1422_, v___x_1421_);
return v___x_1423_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__202(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__201, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__201_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__201);
v___x_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__203(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__202, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__202_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__202);
v___x_1427_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__198, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__198_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__198);
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
lean_ctor_set(v___x_1428_, 1, v___x_1426_);
return v___x_1428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__204(void){
_start:
{
lean_object* v_x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v_x_1429_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__181, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__181_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__181);
v___x_1430_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__203, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__203_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__203);
v___x_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v_x_1429_);
return v___x_1431_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__205(void){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1432_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__204, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__204_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__204);
v___x_1433_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__191, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__191_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__191);
v___x_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v___x_1432_);
return v___x_1434_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__206(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__205, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__205_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__205);
v___x_1436_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__188, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__188_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__188);
v___x_1437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
lean_ctor_set(v___x_1437_, 1, v___x_1435_);
return v___x_1437_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__207(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v_x_1440_; 
v___x_1438_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__206, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__206_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__206);
v___x_1439_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__185, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__185_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__185);
v_x_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1440_, 0, v___x_1439_);
lean_ctor_set(v_x_1440_, 1, v___x_1438_);
return v_x_1440_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208(void){
_start:
{
lean_object* v_int_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_int_1441_ = l_Lean_Int_mkType;
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = lean_mk_empty_array_with_capacity(v___x_1442_);
v___x_1444_ = lean_array_push(v___x_1443_, v_int_1441_);
return v___x_1444_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__209(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_z_1447_; lean_object* v___x_1448_; 
v___x_1445_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208);
v___x_1446_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__120));
v_z_1447_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1448_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1447_, v___x_1446_, v___x_1445_);
return v___x_1448_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__212(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = lean_box(0);
v___x_1453_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__211));
v___x_1454_ = l_Lean_mkConst(v___x_1453_, v___x_1452_);
return v___x_1454_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__213(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__212, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__212_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__212);
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__214(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__213, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__213_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__213);
v___x_1458_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__209, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__209_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__209);
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
lean_ctor_set(v___x_1459_, 1, v___x_1457_);
return v___x_1459_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__215(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v_z_1462_; lean_object* v___x_1463_; 
v___x_1460_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208);
v___x_1461_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__128));
v_z_1462_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1463_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1462_, v___x_1461_, v___x_1460_);
return v___x_1463_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__217(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_box(0);
v___x_1468_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__216));
v___x_1469_ = l_Lean_mkConst(v___x_1468_, v___x_1467_);
return v___x_1469_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__218(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__217, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__217_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__217);
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__219(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__218, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__218_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__218);
v___x_1473_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__215, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__215_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__215);
v___x_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v___x_1472_);
return v___x_1474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__220(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v_z_1477_; lean_object* v___x_1478_; 
v___x_1475_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208);
v___x_1476_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__67));
v_z_1477_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1478_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1477_, v___x_1476_, v___x_1475_);
return v___x_1478_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__222(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = lean_box(0);
v___x_1483_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__221));
v___x_1484_ = l_Lean_mkConst(v___x_1483_, v___x_1482_);
return v___x_1484_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__223(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__222, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__222_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__222);
v___x_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__224(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__223, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__223_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__223);
v___x_1488_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__220, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__220_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__220);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v___x_1487_);
return v___x_1489_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__225(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v_z_1492_; lean_object* v___x_1493_; 
v___x_1490_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68);
v___x_1491_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__75));
v_z_1492_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1493_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1492_, v___x_1491_, v___x_1490_);
return v___x_1493_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__226(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1494_ = lean_box(0);
v___x_1495_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__225, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__225_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__225);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
lean_ctor_set(v___x_1496_, 1, v___x_1494_);
return v___x_1496_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__227(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_z_1499_; lean_object* v___x_1500_; 
v___x_1497_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__68);
v___x_1498_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__79));
v_z_1499_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1500_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1499_, v___x_1498_, v___x_1497_);
return v___x_1500_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__228(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = lean_box(0);
v___x_1502_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__227, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__227_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__227);
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
lean_ctor_set(v___x_1503_, 1, v___x_1501_);
return v___x_1503_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__229(void){
_start:
{
lean_object* v_x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v_x_1504_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__207, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__207_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__207);
v___x_1505_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__228, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__228_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__228);
v___x_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v_x_1504_);
return v___x_1506_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__230(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__229, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__229_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__229);
v___x_1508_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__226, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__226_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__226);
v___x_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v___x_1507_);
return v___x_1509_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__231(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__230, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__230_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__230);
v___x_1511_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__224, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__224_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__224);
v___x_1512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_ctor_set(v___x_1512_, 1, v___x_1510_);
return v___x_1512_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__232(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__231, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__231_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__231);
v___x_1514_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__219, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__219_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__219);
v___x_1515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_ctor_set(v___x_1515_, 1, v___x_1513_);
return v___x_1515_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__233(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v_x_1518_; 
v___x_1516_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__232, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__232_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__232);
v___x_1517_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__214, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__214_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__214);
v_x_1518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1518_, 0, v___x_1517_);
lean_ctor_set(v_x_1518_, 1, v___x_1516_);
return v_x_1518_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234(void){
_start:
{
lean_object* v_leI_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_leI_1519_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__48, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__48_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__48);
v___x_1520_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9);
v___x_1521_ = lean_array_push(v___x_1520_, v_leI_1519_);
return v___x_1521_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__235(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_z_1524_; lean_object* v___x_1525_; 
v___x_1522_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234);
v___x_1523_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__170));
v_z_1524_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1525_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1524_, v___x_1523_, v___x_1522_);
return v___x_1525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__237(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_z_1532_; lean_object* v___x_1533_; 
v___x_1530_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__44, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__44_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__44);
v___x_1531_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__236));
v_z_1532_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1533_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1532_, v___x_1531_, v___x_1530_);
return v___x_1533_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__238(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__237, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__237_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__237);
v___x_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__239(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1536_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__238, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__238_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__238);
v___x_1537_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__235, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__235_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__235);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v___x_1536_);
return v___x_1538_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__240(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v_z_1541_; lean_object* v___x_1542_; 
v___x_1539_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234);
v___x_1540_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__94));
v_z_1541_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1542_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1541_, v___x_1540_, v___x_1539_);
return v___x_1542_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__243(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__242));
v___x_1550_ = l_Lean_mkConst(v___x_1549_, v___x_1548_);
return v___x_1550_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__244(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__243, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__243_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__243);
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
return v___x_1552_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__245(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__244, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__244_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__244);
v___x_1554_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__240, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__240_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__240);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___x_1553_);
return v___x_1555_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__246(void){
_start:
{
lean_object* v_leI_1556_; lean_object* v_ltI_1557_; lean_object* v_int_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v_leI_1556_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__48, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__48_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__48);
v_ltI_1557_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__49, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__49_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__49);
v_int_1558_ = l_Lean_Int_mkType;
v___x_1559_ = lean_unsigned_to_nat(3u);
v___x_1560_ = lean_mk_empty_array_with_capacity(v___x_1559_);
v___x_1561_ = lean_array_push(v___x_1560_, v_int_1558_);
v___x_1562_ = lean_array_push(v___x_1561_, v_ltI_1557_);
v___x_1563_ = lean_array_push(v___x_1562_, v_leI_1556_);
return v___x_1563_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__247(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v_z_1566_; lean_object* v___x_1567_; 
v___x_1564_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__246, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__246_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__246);
v___x_1565_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__100));
v_z_1566_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1567_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1566_, v___x_1565_, v___x_1564_);
return v___x_1567_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__250(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = lean_box(0);
v___x_1574_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__249));
v___x_1575_ = l_Lean_mkConst(v___x_1574_, v___x_1573_);
return v___x_1575_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__251(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__250, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__250_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__250);
v___x_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
return v___x_1577_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__252(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1578_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__251, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__251_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__251);
v___x_1579_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__247, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__247_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__247);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v___x_1578_);
return v___x_1580_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__253(void){
_start:
{
lean_object* v_preI_1581_; lean_object* v_ltI_1582_; lean_object* v_leI_1583_; lean_object* v_srI_1584_; lean_object* v_int_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_preI_1581_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__47, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__47_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__47);
v_ltI_1582_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__49, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__49_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__49);
v_leI_1583_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__48, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__48_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__48);
v_srI_1584_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__16, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__16_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__16);
v_int_1585_ = l_Lean_Int_mkType;
v___x_1586_ = lean_unsigned_to_nat(5u);
v___x_1587_ = lean_mk_empty_array_with_capacity(v___x_1586_);
v___x_1588_ = lean_array_push(v___x_1587_, v_int_1585_);
v___x_1589_ = lean_array_push(v___x_1588_, v_srI_1584_);
v___x_1590_ = lean_array_push(v___x_1589_, v_leI_1583_);
v___x_1591_ = lean_array_push(v___x_1590_, v_ltI_1582_);
v___x_1592_ = lean_array_push(v___x_1591_, v_preI_1581_);
return v___x_1592_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__254(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v_z_1595_; lean_object* v___x_1596_; 
v___x_1593_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__253, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__253_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__253);
v___x_1594_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__111));
v_z_1595_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1596_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1595_, v___x_1594_, v___x_1593_);
return v___x_1596_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__257(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1602_ = lean_box(0);
v___x_1603_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__256));
v___x_1604_ = l_Lean_mkConst(v___x_1603_, v___x_1602_);
return v___x_1604_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__258(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__257, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__257_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__257);
v___x_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
return v___x_1606_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__259(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__258, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__258_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__258);
v___x_1608_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__254, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__254_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__254);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_ctor_set(v___x_1609_, 1, v___x_1607_);
return v___x_1609_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__260(void){
_start:
{
lean_object* v_x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_x_1610_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__233, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__233_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__233);
v___x_1611_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__259, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__259_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__259);
v___x_1612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_ctor_set(v___x_1612_, 1, v_x_1610_);
return v___x_1612_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__261(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__260, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__260_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__260);
v___x_1614_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__252, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__252_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__252);
v___x_1615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
lean_ctor_set(v___x_1615_, 1, v___x_1613_);
return v___x_1615_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__262(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__261, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__261_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__261);
v___x_1617_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__245, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__245_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__245);
v___x_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_ctor_set(v___x_1618_, 1, v___x_1616_);
return v___x_1618_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__263(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v_x_1621_; 
v___x_1619_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__262, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__262_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__262);
v___x_1620_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__239, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__239_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__239);
v_x_1621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1621_, 0, v___x_1620_);
lean_ctor_set(v_x_1621_, 1, v___x_1619_);
return v_x_1621_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__264(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v_z_1624_; lean_object* v___x_1625_; 
v___x_1622_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208);
v___x_1623_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__183));
v_z_1624_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1625_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1624_, v___x_1623_, v___x_1622_);
return v___x_1625_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__265(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__264, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__264_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__264);
v___x_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
lean_ctor_set(v___x_1628_, 1, v___x_1626_);
return v___x_1628_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__266(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v_z_1631_; lean_object* v___x_1632_; 
v___x_1629_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208);
v___x_1630_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__141));
v_z_1631_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1632_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1631_, v___x_1630_, v___x_1629_);
return v___x_1632_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__267(void){
_start:
{
lean_object* v_nmI_1633_; lean_object* v___x_1634_; 
v_nmI_1633_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__28, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__28_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__28);
v___x_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1634_, 0, v_nmI_1633_);
return v___x_1634_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__268(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__267, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__267_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__267);
v___x_1636_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__266, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__266_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__266);
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v___x_1635_);
return v___x_1637_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__269(void){
_start:
{
lean_object* v_nmI_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_nmI_1638_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__28, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__28_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__28);
v___x_1639_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9);
v___x_1640_ = lean_array_push(v___x_1639_, v_nmI_1638_);
return v___x_1640_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__270(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_z_1643_; lean_object* v___x_1644_; 
v___x_1641_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__269, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__269_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__269);
v___x_1642_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__146));
v_z_1643_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1644_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1643_, v___x_1642_, v___x_1641_);
return v___x_1644_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__273(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1650_ = lean_box(0);
v___x_1651_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__272));
v___x_1652_ = l_Lean_mkConst(v___x_1651_, v___x_1650_);
return v___x_1652_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__274(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__273, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__273_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__273);
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__275(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1655_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__274, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__274_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__274);
v___x_1656_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__270, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__270_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__270);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_ctor_set(v___x_1657_, 1, v___x_1655_);
return v___x_1657_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__276(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v_z_1660_; lean_object* v___x_1661_; 
v___x_1658_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234);
v___x_1659_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__155));
v_z_1660_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1661_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1660_, v___x_1659_, v___x_1658_);
return v___x_1661_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__277(void){
_start:
{
lean_object* v_preI_1662_; lean_object* v___x_1663_; 
v_preI_1662_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__47, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__47_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__47);
v___x_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_preI_1662_);
return v___x_1663_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__278(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__277, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__277_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__277);
v___x_1665_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__276, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__276_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__276);
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set(v___x_1666_, 1, v___x_1664_);
return v___x_1666_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__279(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v_z_1669_; lean_object* v___x_1670_; 
v___x_1667_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__234);
v___x_1668_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__160));
v_z_1669_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1670_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1669_, v___x_1668_, v___x_1667_);
return v___x_1670_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__284(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v_z_1683_; lean_object* v___x_1684_; 
v___x_1681_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__36);
v___x_1682_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__283));
v_z_1683_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1684_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1683_, v___x_1682_, v___x_1681_);
return v___x_1684_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__285(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__284, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__284_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__284);
v___x_1686_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__9);
v___x_1687_ = lean_array_push(v___x_1686_, v___x_1685_);
return v___x_1687_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__286(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v_z_1690_; lean_object* v___x_1691_; 
v___x_1688_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__285, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__285_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__285);
v___x_1689_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__281));
v_z_1690_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1691_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1690_, v___x_1689_, v___x_1688_);
return v___x_1691_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__287(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__286, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__286_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__286);
v___x_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
return v___x_1693_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__288(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__287, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__287_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__287);
v___x_1695_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__279, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__279_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__279);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
lean_ctor_set(v___x_1696_, 1, v___x_1694_);
return v___x_1696_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__289(void){
_start:
{
lean_object* v_x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_x_1697_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__263, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__263_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__263);
v___x_1698_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__288, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__288_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__288);
v___x_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v_x_1697_);
return v___x_1699_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__290(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1700_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__289, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__289_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__289);
v___x_1701_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__278, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__278_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__278);
v___x_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
lean_ctor_set(v___x_1702_, 1, v___x_1700_);
return v___x_1702_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__291(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__290, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__290_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__290);
v___x_1704_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__275, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__275_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__275);
v___x_1705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v___x_1703_);
return v___x_1705_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__292(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__291, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__291_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__291);
v___x_1707_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__268, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__268_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__268);
v___x_1708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v___x_1706_);
return v___x_1708_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__293(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v_x_1711_; 
v___x_1709_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__292, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__292_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__292);
v___x_1710_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__265, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__265_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__265);
v_x_1711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1711_, 0, v___x_1710_);
lean_ctor_set(v_x_1711_, 1, v___x_1709_);
return v_x_1711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__294(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v_z_1714_; lean_object* v___x_1715_; 
v___x_1712_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208);
v___x_1713_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__75));
v_z_1714_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1715_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1714_, v___x_1713_, v___x_1712_);
return v___x_1715_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__295(void){
_start:
{
lean_object* v_crI_1716_; lean_object* v___x_1717_; 
v_crI_1716_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__5, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__5_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__5);
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_crI_1716_);
return v___x_1717_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__296(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__295, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__295_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__295);
v___x_1719_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__294, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__294_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__294);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
lean_ctor_set(v___x_1720_, 1, v___x_1718_);
return v___x_1720_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__297(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v_z_1723_; lean_object* v___x_1724_; 
v___x_1721_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208);
v___x_1722_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__79));
v_z_1723_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1724_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1723_, v___x_1722_, v___x_1721_);
return v___x_1724_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__298(void){
_start:
{
lean_object* v_ringI_1725_; lean_object* v___x_1726_; 
v_ringI_1725_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__11, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__11_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__11);
v___x_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1726_, 0, v_ringI_1725_);
return v___x_1726_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__299(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__298, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__298_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__298);
v___x_1728_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__297, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__297_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__297);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v___x_1727_);
return v___x_1729_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__300(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v_z_1732_; lean_object* v___x_1733_; 
v___x_1730_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208);
v___x_1731_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__82));
v_z_1732_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1733_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1732_, v___x_1731_, v___x_1730_);
return v___x_1733_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__301(void){
_start:
{
lean_object* v_csI_1734_; lean_object* v___x_1735_; 
v_csI_1734_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__19, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__19_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__19);
v___x_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1735_, 0, v_csI_1734_);
return v___x_1735_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__302(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__301, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__301_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__301);
v___x_1737_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__300, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__300_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__300);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
lean_ctor_set(v___x_1738_, 1, v___x_1736_);
return v___x_1738_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__303(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v_z_1741_; lean_object* v___x_1742_; 
v___x_1739_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__208);
v___x_1740_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__85));
v_z_1741_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0));
v___x_1742_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___lam__0(v_z_1741_, v___x_1740_, v___x_1739_);
return v___x_1742_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__304(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__26, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__26_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__26);
v___x_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__305(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__304, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__304_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__304);
v___x_1746_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__303, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__303_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__303);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set(v___x_1747_, 1, v___x_1745_);
return v___x_1747_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__306(void){
_start:
{
lean_object* v_x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v_x_1748_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__293, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__293_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__293);
v___x_1749_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__305, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__305_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__305);
v___x_1750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v_x_1748_);
return v___x_1750_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__307(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__306, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__306_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__306);
v___x_1752_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__302, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__302_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__302);
v___x_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v___x_1751_);
return v___x_1753_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__308(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__307, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__307_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__307);
v___x_1755_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__299, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__299_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__299);
v___x_1756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v___x_1754_);
return v___x_1756_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__309(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__308, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__308_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__308);
v___x_1758_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__296, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__296_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__296);
v___x_1759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___x_1757_);
return v___x_1759_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__310(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__148, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__148_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__148);
v___x_1761_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__309, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__309_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__309);
v___x_1762_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0_spec__0___redArg(v___x_1761_, v___x_1760_);
return v___x_1762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts(void){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__310, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__310_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__310);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0_spec__0(lean_object* v_as_1764_, lean_object* v_as_x27_1765_, lean_object* v_b_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0_spec__0___redArg(v_as_x27_1765_, v_b_1766_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0_spec__0___boxed(lean_object* v_as_1769_, lean_object* v_as_x27_1770_, lean_object* v_b_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts_spec__0_spec__0(v_as_1769_, v_as_x27_1770_, v_b_1771_, v_a_1772_);
lean_dec(v_as_x27_1770_);
lean_dec(v_as_1769_);
return v_res_1773_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__0(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36);
v___x_1775_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__14));
v___x_1776_ = l_Lean_mkConst(v___x_1775_, v___x_1774_);
return v___x_1776_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__1(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36);
v___x_1778_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__8));
v___x_1779_ = l_Lean_mkConst(v___x_1778_, v___x_1777_);
return v___x_1779_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__2(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1780_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__5, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__5_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__5);
v___x_1781_ = l_Lean_Int_mkType;
v___x_1782_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__1, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__1_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__1);
v___x_1783_ = l_Lean_mkAppB(v___x_1782_, v___x_1781_, v___x_1780_);
return v___x_1783_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__3(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1784_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__2, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__2_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__2);
v___x_1785_ = l_Lean_Int_mkType;
v___x_1786_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__0, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__0_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__0);
v___x_1787_ = l_Lean_mkAppB(v___x_1786_, v___x_1785_, v___x_1784_);
return v___x_1787_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring(void){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__3, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__3_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__3);
return v___x_1788_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__0(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36);
v___x_1790_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__24));
v___x_1791_ = l_Lean_mkConst(v___x_1790_, v___x_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__1(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1792_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__52, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__52_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts___closed__52);
v___x_1793_ = l_Lean_Nat_mkType;
v___x_1794_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__0, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__0_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__0);
v___x_1795_ = l_Lean_mkAppB(v___x_1794_, v___x_1793_, v___x_1792_);
return v___x_1795_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring(void){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__1, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__1_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__1);
return v___x_1796_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared(lean_object* v_env_1797_, lean_object* v_x_1798_){
_start:
{
switch(lean_obj_tag(v_x_1798_))
{
case 4:
{
lean_object* v_declName_1799_; uint8_t v___x_1800_; uint8_t v___x_1801_; 
v_declName_1799_ = lean_ctor_get(v_x_1798_, 0);
lean_inc(v_declName_1799_);
lean_dec_ref_known(v_x_1798_, 2);
v___x_1800_ = 1;
v___x_1801_ = l_Lean_Environment_contains(v_env_1797_, v_declName_1799_, v___x_1800_);
return v___x_1801_;
}
case 5:
{
lean_object* v_fn_1802_; lean_object* v_arg_1803_; uint8_t v___x_1804_; 
v_fn_1802_ = lean_ctor_get(v_x_1798_, 0);
lean_inc_ref(v_fn_1802_);
v_arg_1803_ = lean_ctor_get(v_x_1798_, 1);
lean_inc_ref(v_arg_1803_);
lean_dec_ref_known(v_x_1798_, 2);
lean_inc_ref(v_env_1797_);
v___x_1804_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared(v_env_1797_, v_fn_1802_);
if (v___x_1804_ == 0)
{
lean_dec_ref(v_arg_1803_);
lean_dec_ref(v_env_1797_);
return v___x_1804_;
}
else
{
v_x_1798_ = v_arg_1803_;
goto _start;
}
}
default: 
{
uint8_t v___x_1806_; 
lean_dec_ref(v_x_1798_);
lean_dec_ref(v_env_1797_);
v___x_1806_ = 1;
return v___x_1806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared___boxed(lean_object* v_env_1807_, lean_object* v_x_1808_){
_start:
{
uint8_t v_res_1809_; lean_object* v_r_1810_; 
v_res_1809_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared(v_env_1807_, v_x_1808_);
v_r_1810_ = lean_box(v_res_1809_);
return v_r_1810_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__7(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = lean_box(0);
v___x_1829_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6));
v___x_1830_ = l_Lean_mkConst(v___x_1829_, v___x_1828_);
return v___x_1830_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__10(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = lean_box(0);
v___x_1837_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__9));
v___x_1838_ = l_Lean_mkConst(v___x_1837_, v___x_1836_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f(lean_object* v_type_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_type_1839_, v_a_1841_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1938_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1938_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1938_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = l_Lean_Expr_cleanupAnnotations(v_a_1849_);
lean_dec(v_a_1849_);
v___x_1862_ = l_Lean_Expr_isApp(v___x_1861_);
if (v___x_1862_ == 0)
{
lean_dec_ref(v___x_1861_);
lean_del_object(v___x_1851_);
goto v___jp_1845_;
}
else
{
lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1861_);
v___x_1864_ = l_Lean_Expr_isApp(v___x_1863_);
if (v___x_1864_ == 0)
{
lean_dec_ref(v___x_1863_);
lean_dec_ref(v___x_1861_);
lean_del_object(v___x_1851_);
goto v___jp_1845_;
}
else
{
lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1865_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1863_);
v___x_1866_ = l_Lean_Expr_isApp(v___x_1865_);
if (v___x_1866_ == 0)
{
lean_dec_ref(v___x_1865_);
lean_dec_ref(v___x_1863_);
lean_dec_ref(v___x_1861_);
lean_del_object(v___x_1851_);
goto v___jp_1845_;
}
else
{
lean_object* v_arg_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v_arg_1867_ = lean_ctor_get(v___x_1865_, 1);
lean_inc_ref(v_arg_1867_);
v___x_1868_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1865_);
lean_dec_ref(v___x_1865_);
v___x_1869_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2));
v___x_1870_ = l_Lean_Expr_isConstOf(v___x_1868_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; uint8_t v___x_1872_; 
lean_del_object(v___x_1851_);
v___x_1871_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4));
v___x_1872_ = l_Lean_Expr_isConstOf(v___x_1868_, v___x_1871_);
lean_dec_ref(v___x_1868_);
if (v___x_1872_ == 0)
{
lean_dec_ref(v_arg_1867_);
lean_dec_ref(v___x_1863_);
lean_dec_ref(v___x_1861_);
goto v___jp_1845_;
}
else
{
lean_object* v_arg_1873_; lean_object* v_inst_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v_arg_1920_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
v_arg_1873_ = lean_ctor_get(v___x_1861_, 1);
lean_inc_ref(v_arg_1873_);
lean_dec_ref(v___x_1861_);
v_arg_1920_ = lean_ctor_get(v___x_1863_, 1);
lean_inc_ref(v_arg_1920_);
lean_dec_ref(v___x_1863_);
v___x_1927_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5));
v___x_1928_ = l_Lean_Expr_isConstOf(v_arg_1867_, v___x_1927_);
if (v___x_1928_ == 0)
{
goto v___jp_1921_;
}
else
{
lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring;
v___x_1930_ = lean_expr_eqv(v_arg_1920_, v___x_1929_);
if (v___x_1930_ == 0)
{
goto v___jp_1921_;
}
else
{
lean_object* v___x_1931_; 
lean_dec_ref(v_arg_1920_);
lean_dec_ref(v_arg_1867_);
v___x_1931_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__10, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__10_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__10);
v_inst_1875_ = v___x_1931_;
v___y_1876_ = v_a_1840_;
v___y_1877_ = v_a_1841_;
v___y_1878_ = v_a_1842_;
v___y_1879_ = v_a_1843_;
goto v___jp_1874_;
}
}
v___jp_1874_:
{
lean_object* v___x_1880_; lean_object* v_env_1881_; uint8_t v___x_1882_; 
v___x_1880_ = lean_st_ref_get(v___y_1879_);
v_env_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc_ref(v_env_1881_);
lean_dec(v___x_1880_);
lean_inc_ref(v_inst_1875_);
v___x_1882_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared(v_env_1881_, v_inst_1875_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_dec_ref(v_arg_1873_);
v___x_1883_ = lean_box(0);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; 
lean_inc(v___y_1879_);
lean_inc_ref(v___y_1878_);
lean_inc(v___y_1877_);
lean_inc_ref(v___y_1876_);
lean_inc_ref(v_inst_1875_);
v___x_1885_ = lean_infer_type(v_inst_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = l_Lean_Expr_appArg_x21(v_a_1886_);
lean_dec(v_a_1886_);
v___x_1888_ = l_Lean_Meta_isExprDefEq(v_arg_1873_, v___x_1887_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1903_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1903_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1903_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_unbox(v_a_1889_);
lean_dec(v_a_1889_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = lean_box(0);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1894_);
v___x_1896_ = v___x_1891_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
lean_inc_ref(v_inst_1875_);
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v_inst_1875_);
v___x_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1899_);
v___x_1901_ = v___x_1891_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
v_a_1904_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1888_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1888_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec_ref(v_arg_1873_);
v_a_1912_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1885_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1885_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
v___jp_1921_:
{
lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1922_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__7));
v___x_1923_ = l_Lean_Expr_isConstOf(v_arg_1867_, v___x_1922_);
lean_dec_ref(v_arg_1867_);
if (v___x_1923_ == 0)
{
lean_dec_ref(v_arg_1920_);
lean_dec_ref(v_arg_1873_);
goto v___jp_1858_;
}
else
{
lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1924_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring;
v___x_1925_ = lean_expr_eqv(v_arg_1920_, v___x_1924_);
lean_dec_ref(v_arg_1920_);
if (v___x_1925_ == 0)
{
lean_dec_ref(v_arg_1873_);
goto v___jp_1858_;
}
else
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__7, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__7_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__7);
v_inst_1875_ = v___x_1926_;
v___y_1876_ = v_a_1840_;
v___y_1877_ = v_a_1841_;
v___y_1878_ = v_a_1842_;
v___y_1879_ = v_a_1843_;
goto v___jp_1874_;
}
}
}
}
}
else
{
lean_object* v___x_1932_; uint8_t v___x_1933_; 
lean_dec_ref(v___x_1868_);
lean_dec_ref(v___x_1863_);
lean_dec_ref(v___x_1861_);
v___x_1932_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5));
v___x_1933_ = l_Lean_Expr_isConstOf(v_arg_1867_, v___x_1932_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1934_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__7));
v___x_1935_ = l_Lean_Expr_isConstOf(v_arg_1867_, v___x_1934_);
lean_dec_ref(v_arg_1867_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_del_object(v___x_1851_);
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
else
{
goto v___jp_1853_;
}
}
else
{
lean_dec_ref(v_arg_1867_);
goto v___jp_1853_;
}
}
}
}
}
v___jp_1853_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__0));
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1854_);
v___x_1856_ = v___x_1851_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
v___jp_1858_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_box(0);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
return v___x_1860_;
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1939_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1848_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1848_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
v___jp_1845_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_box(0);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___boxed(lean_object* v_type_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f(v_type_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(lean_object* v_category_1954_, lean_object* v_opts_1955_, lean_object* v_act_1956_, lean_object* v_decl_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_inc(v___y_1961_);
lean_inc_ref(v___y_1960_);
lean_inc(v___y_1959_);
lean_inc_ref(v___y_1958_);
v___x_1963_ = lean_apply_4(v_act_1956_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
v___x_1964_ = l_Lean_profileitIOUnsafe___redArg(v_category_1954_, v_opts_1955_, v___x_1963_, v_decl_1957_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg___boxed(lean_object* v_category_1965_, lean_object* v_opts_1966_, lean_object* v_act_1967_, lean_object* v_decl_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v_category_1965_, v_opts_1966_, v_act_1967_, v_decl_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec_ref(v_opts_1966_);
lean_dec_ref(v_category_1965_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(lean_object* v_00_u03b1_1975_, lean_object* v_category_1976_, lean_object* v_opts_1977_, lean_object* v_act_1978_, lean_object* v_decl_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v_category_1976_, v_opts_1977_, v_act_1978_, v_decl_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___boxed(lean_object* v_00_u03b1_1986_, lean_object* v_category_1987_, lean_object* v_opts_1988_, lean_object* v_act_1989_, lean_object* v_decl_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(v_00_u03b1_1986_, v_category_1987_, v_opts_1988_, v_act_1989_, v_decl_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v_opts_1988_);
lean_dec_ref(v_category_1987_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(lean_object* v___x_1997_, lean_object* v_type_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; 
if (lean_obj_tag(v___x_1997_) == 1)
{
lean_object* v___x_2043_; 
lean_dec_ref(v_type_1998_);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_1997_);
return v___x_2043_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec(v___x_1997_);
v___x_2044_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts;
v___x_2045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v___x_2044_, v_type_1998_);
if (lean_obj_tag(v___x_2045_) == 1)
{
lean_object* v_val_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2060_; 
v_val_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2060_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_val_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2060_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_st_ref_get(v___y_2002_);
if (lean_obj_tag(v_val_2046_) == 0)
{
lean_object* v___x_2052_; 
lean_dec(v___x_2050_);
lean_dec_ref(v_type_1998_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set_tag(v___x_2048_, 0);
v___x_2052_ = v___x_2048_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_val_2046_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
else
{
lean_object* v_val_2054_; lean_object* v_env_2055_; uint8_t v___x_2056_; 
v_val_2054_ = lean_ctor_get(v_val_2046_, 0);
v_env_2055_ = lean_ctor_get(v___x_2050_, 0);
lean_inc_ref(v_env_2055_);
lean_dec(v___x_2050_);
lean_inc(v_val_2054_);
v___x_2056_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared(v_env_2055_, v_val_2054_);
if (v___x_2056_ == 0)
{
lean_dec_ref_known(v_val_2046_, 1);
lean_del_object(v___x_2048_);
v___y_2005_ = v___y_1999_;
v___y_2006_ = v___y_2000_;
v___y_2007_ = v___y_2001_;
v___y_2008_ = v___y_2002_;
goto v___jp_2004_;
}
else
{
lean_object* v___x_2058_; 
lean_dec_ref(v_type_1998_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set_tag(v___x_2048_, 0);
v___x_2058_ = v___x_2048_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_val_2046_);
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
}
else
{
lean_dec(v___x_2045_);
v___y_2005_ = v___y_1999_;
v___y_2006_ = v___y_2000_;
v___y_2007_ = v___y_2001_;
v___y_2008_ = v___y_2002_;
goto v___jp_2004_;
}
}
v___jp_2004_:
{
lean_object* v___x_2009_; 
lean_inc_ref(v_type_1998_);
v___x_2009_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f(v_type_1998_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2034_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2034_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2034_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
if (lean_obj_tag(v_a_2010_) == 1)
{
lean_object* v_val_2014_; lean_object* v___x_2016_; 
lean_dec_ref(v_type_1998_);
v_val_2014_ = lean_ctor_get(v_a_2010_, 0);
lean_inc(v_val_2014_);
lean_dec_ref_known(v_a_2010_, 1);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v_val_2014_);
v___x_2016_ = v___x_2012_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_val_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_del_object(v___x_2012_);
lean_dec(v_a_2010_);
v___x_2018_ = l_Lean_Meta_isDefEqStuckExceptionId;
v___x_2019_ = lean_box(0);
v___x_2020_ = l_Lean_Meta_synthInstanceCore_x3f(v_type_1998_, v___x_2019_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2020_) == 0)
{
return v___x_2020_;
}
else
{
lean_object* v_a_2021_; uint8_t v___x_2022_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v___x_2022_ = l_Lean_Exception_isInterrupt(v_a_2021_);
if (v___x_2022_ == 0)
{
uint8_t v___x_2023_; 
lean_inc(v_a_2021_);
v___x_2023_ = l_Lean_Exception_isRuntime(v_a_2021_);
if (v___x_2023_ == 0)
{
if (lean_obj_tag(v_a_2021_) == 0)
{
return v___x_2020_;
}
else
{
lean_object* v_id_2024_; uint8_t v___x_2025_; 
v_id_2024_ = lean_ctor_get(v_a_2021_, 0);
v___x_2025_ = l_Lean_instBEqInternalExceptionId_beq(v___x_2018_, v_id_2024_);
if (v___x_2025_ == 0)
{
return v___x_2020_;
}
else
{
lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; 
v_unused_2033_ = lean_ctor_get(v___x_2020_, 0);
lean_dec(v_unused_2033_);
v___x_2027_ = v___x_2020_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_dec(v___x_2020_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set_tag(v___x_2027_, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2019_);
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2019_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
else
{
return v___x_2020_;
}
}
else
{
return v___x_2020_;
}
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v_type_1998_);
v_a_2035_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2009_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2009_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed(lean_object* v___x_2061_, lean_object* v_type_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(v___x_2061_, v_type_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object* v_type_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___y_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2076_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2073_);
v___x_2077_ = ((lean_object*)(l_Lean_Meta_Sym_synthInstanceMeta_x3f___closed__0));
v___x_2078_ = l_Lean_Meta_Sym_getBuiltinInstance_x3f(v_type_2070_);
lean_inc_ref(v_type_2070_);
v___y_2079_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___y_2079_, 0, v___x_2078_);
lean_closure_set(v___y_2079_, 1, v_type_2070_);
v___x_2080_ = l_Lean_Expr_getAppFn(v_type_2070_);
lean_dec_ref(v_type_2070_);
v___x_2081_ = l_Lean_Expr_constName_x3f(v___x_2080_);
lean_dec_ref(v___x_2080_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = lean_box(0);
v___x_2083_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v___x_2077_, v___x_2076_, v___y_2079_, v___x_2082_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
lean_dec_ref(v___x_2076_);
return v___x_2083_;
}
else
{
lean_object* v_val_2084_; lean_object* v___x_2085_; 
v_val_2084_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_val_2084_);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2085_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v___x_2077_, v___x_2076_, v___y_2079_, v_val_2084_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
lean_dec_ref(v___x_2076_);
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___boxed(lean_object* v_type_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2093_, lean_object* v_x_2094_, lean_object* v_x_2095_, lean_object* v_x_2096_){
_start:
{
lean_object* v_ks_2097_; lean_object* v_vs_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2122_; 
v_ks_2097_ = lean_ctor_get(v_x_2093_, 0);
v_vs_2098_ = lean_ctor_get(v_x_2093_, 1);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_x_2093_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2100_ = v_x_2093_;
v_isShared_2101_ = v_isSharedCheck_2122_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_vs_2098_);
lean_inc(v_ks_2097_);
lean_dec(v_x_2093_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2122_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = lean_array_get_size(v_ks_2097_);
v___x_2103_ = lean_nat_dec_lt(v_x_2094_, v___x_2102_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
lean_dec(v_x_2094_);
v___x_2104_ = lean_array_push(v_ks_2097_, v_x_2095_);
v___x_2105_ = lean_array_push(v_vs_2098_, v_x_2096_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 1, v___x_2105_);
lean_ctor_set(v___x_2100_, 0, v___x_2104_);
v___x_2107_ = v___x_2100_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
else
{
lean_object* v_k_x27_2109_; uint8_t v___x_2110_; 
v_k_x27_2109_ = lean_array_fget_borrowed(v_ks_2097_, v_x_2094_);
v___x_2110_ = lean_expr_eqv(v_x_2095_, v_k_x27_2109_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2112_; 
if (v_isShared_2101_ == 0)
{
v___x_2112_ = v___x_2100_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_ks_2097_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_vs_2098_);
v___x_2112_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_unsigned_to_nat(1u);
v___x_2114_ = lean_nat_add(v_x_2094_, v___x_2113_);
lean_dec(v_x_2094_);
v_x_2093_ = v___x_2112_;
v_x_2094_ = v___x_2114_;
goto _start;
}
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2117_ = lean_array_fset(v_ks_2097_, v_x_2094_, v_x_2095_);
v___x_2118_ = lean_array_fset(v_vs_2098_, v_x_2094_, v_x_2096_);
lean_dec(v_x_2094_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 1, v___x_2118_);
lean_ctor_set(v___x_2100_, 0, v___x_2117_);
v___x_2120_ = v___x_2100_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2123_, lean_object* v_k_2124_, lean_object* v_v_2125_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2123_, v___x_2126_, v_k_2124_, v_v_2125_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(lean_object* v_x_2129_, size_t v_x_2130_, size_t v_x_2131_, lean_object* v_x_2132_, lean_object* v_x_2133_){
_start:
{
if (lean_obj_tag(v_x_2129_) == 0)
{
lean_object* v_es_2134_; size_t v___x_2135_; size_t v___x_2136_; lean_object* v_j_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v_es_2134_ = lean_ctor_get(v_x_2129_, 0);
v___x_2135_ = ((size_t)31ULL);
v___x_2136_ = lean_usize_land(v_x_2130_, v___x_2135_);
v_j_2137_ = lean_usize_to_nat(v___x_2136_);
v___x_2138_ = lean_array_get_size(v_es_2134_);
v___x_2139_ = lean_nat_dec_lt(v_j_2137_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_dec(v_j_2137_);
lean_dec(v_x_2133_);
lean_dec_ref(v_x_2132_);
return v_x_2129_;
}
else
{
lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2178_; 
lean_inc_ref(v_es_2134_);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_x_2129_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; 
v_unused_2179_ = lean_ctor_get(v_x_2129_, 0);
lean_dec(v_unused_2179_);
v___x_2141_ = v_x_2129_;
v_isShared_2142_ = v_isSharedCheck_2178_;
goto v_resetjp_2140_;
}
else
{
lean_dec(v_x_2129_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2178_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_v_2143_; lean_object* v___x_2144_; lean_object* v_xs_x27_2145_; lean_object* v___y_2147_; 
v_v_2143_ = lean_array_fget(v_es_2134_, v_j_2137_);
v___x_2144_ = lean_box(0);
v_xs_x27_2145_ = lean_array_fset(v_es_2134_, v_j_2137_, v___x_2144_);
switch(lean_obj_tag(v_v_2143_))
{
case 0:
{
lean_object* v_key_2152_; lean_object* v_val_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2163_; 
v_key_2152_ = lean_ctor_get(v_v_2143_, 0);
v_val_2153_ = lean_ctor_get(v_v_2143_, 1);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_v_2143_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2155_ = v_v_2143_;
v_isShared_2156_ = v_isSharedCheck_2163_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_val_2153_);
lean_inc(v_key_2152_);
lean_dec(v_v_2143_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2163_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
uint8_t v___x_2157_; 
v___x_2157_ = lean_expr_eqv(v_x_2132_, v_key_2152_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
lean_del_object(v___x_2155_);
v___x_2158_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2152_, v_val_2153_, v_x_2132_, v_x_2133_);
v___x_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
v___y_2147_ = v___x_2159_;
goto v___jp_2146_;
}
else
{
lean_object* v___x_2161_; 
lean_dec(v_val_2153_);
lean_dec(v_key_2152_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v_x_2133_);
lean_ctor_set(v___x_2155_, 0, v_x_2132_);
v___x_2161_ = v___x_2155_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_x_2132_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_x_2133_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
v___y_2147_ = v___x_2161_;
goto v___jp_2146_;
}
}
}
}
case 1:
{
lean_object* v_node_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2176_; 
v_node_2164_ = lean_ctor_get(v_v_2143_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_v_2143_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2166_ = v_v_2143_;
v_isShared_2167_ = v_isSharedCheck_2176_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_node_2164_);
lean_dec(v_v_2143_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2176_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
size_t v___x_2168_; size_t v___x_2169_; size_t v___x_2170_; size_t v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2168_ = ((size_t)5ULL);
v___x_2169_ = lean_usize_shift_right(v_x_2130_, v___x_2168_);
v___x_2170_ = ((size_t)1ULL);
v___x_2171_ = lean_usize_add(v_x_2131_, v___x_2170_);
v___x_2172_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_node_2164_, v___x_2169_, v___x_2171_, v_x_2132_, v_x_2133_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2172_);
v___x_2174_ = v___x_2166_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
v___y_2147_ = v___x_2174_;
goto v___jp_2146_;
}
}
}
default: 
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v_x_2132_);
lean_ctor_set(v___x_2177_, 1, v_x_2133_);
v___y_2147_ = v___x_2177_;
goto v___jp_2146_;
}
}
v___jp_2146_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = lean_array_fset(v_xs_x27_2145_, v_j_2137_, v___y_2147_);
lean_dec(v_j_2137_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v___x_2148_);
v___x_2150_ = v___x_2141_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
else
{
lean_object* v_ks_2180_; lean_object* v_vs_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2199_; 
v_ks_2180_ = lean_ctor_get(v_x_2129_, 0);
v_vs_2181_ = lean_ctor_get(v_x_2129_, 1);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_x_2129_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2183_ = v_x_2129_;
v_isShared_2184_ = v_isSharedCheck_2199_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_vs_2181_);
lean_inc(v_ks_2180_);
lean_dec(v_x_2129_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2199_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_ks_2180_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_vs_2181_);
v___x_2186_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v_newNode_2187_; size_t v___x_2188_; uint8_t v___x_2189_; 
v_newNode_2187_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(v___x_2186_, v_x_2132_, v_x_2133_);
v___x_2188_ = ((size_t)7ULL);
v___x_2189_ = lean_usize_dec_le(v___x_2188_, v_x_2131_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2190_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2187_);
v___x_2191_ = lean_unsigned_to_nat(4u);
v___x_2192_ = lean_nat_dec_lt(v___x_2190_, v___x_2191_);
lean_dec(v___x_2190_);
if (v___x_2192_ == 0)
{
lean_object* v_ks_2193_; lean_object* v_vs_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v_ks_2193_ = lean_ctor_get(v_newNode_2187_, 0);
lean_inc_ref(v_ks_2193_);
v_vs_2194_ = lean_ctor_get(v_newNode_2187_, 1);
lean_inc_ref(v_vs_2194_);
lean_dec_ref(v_newNode_2187_);
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0);
v___x_2197_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_x_2131_, v_ks_2193_, v_vs_2194_, v___x_2195_, v___x_2196_);
lean_dec_ref(v_vs_2194_);
lean_dec_ref(v_ks_2193_);
return v___x_2197_;
}
else
{
return v_newNode_2187_;
}
}
else
{
return v_newNode_2187_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(size_t v_depth_2200_, lean_object* v_keys_2201_, lean_object* v_vals_2202_, lean_object* v_i_2203_, lean_object* v_entries_2204_){
_start:
{
lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2205_ = lean_array_get_size(v_keys_2201_);
v___x_2206_ = lean_nat_dec_lt(v_i_2203_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_dec(v_i_2203_);
return v_entries_2204_;
}
else
{
lean_object* v_k_2207_; lean_object* v_v_2208_; uint64_t v___x_2209_; size_t v_h_2210_; size_t v___x_2211_; lean_object* v___x_2212_; size_t v___x_2213_; size_t v___x_2214_; size_t v___x_2215_; size_t v_h_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v_k_2207_ = lean_array_fget_borrowed(v_keys_2201_, v_i_2203_);
v_v_2208_ = lean_array_fget_borrowed(v_vals_2202_, v_i_2203_);
v___x_2209_ = l_Lean_Expr_hash(v_k_2207_);
v_h_2210_ = lean_uint64_to_usize(v___x_2209_);
v___x_2211_ = ((size_t)5ULL);
v___x_2212_ = lean_unsigned_to_nat(1u);
v___x_2213_ = ((size_t)1ULL);
v___x_2214_ = lean_usize_sub(v_depth_2200_, v___x_2213_);
v___x_2215_ = lean_usize_mul(v___x_2211_, v___x_2214_);
v_h_2216_ = lean_usize_shift_right(v_h_2210_, v___x_2215_);
v___x_2217_ = lean_nat_add(v_i_2203_, v___x_2212_);
lean_dec(v_i_2203_);
lean_inc(v_v_2208_);
lean_inc(v_k_2207_);
v___x_2218_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_entries_2204_, v_h_2216_, v_depth_2200_, v_k_2207_, v_v_2208_);
v_i_2203_ = v___x_2217_;
v_entries_2204_ = v___x_2218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2220_, lean_object* v_keys_2221_, lean_object* v_vals_2222_, lean_object* v_i_2223_, lean_object* v_entries_2224_){
_start:
{
size_t v_depth_boxed_2225_; lean_object* v_res_2226_; 
v_depth_boxed_2225_ = lean_unbox_usize(v_depth_2220_);
lean_dec(v_depth_2220_);
v_res_2226_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2225_, v_keys_2221_, v_vals_2222_, v_i_2223_, v_entries_2224_);
lean_dec_ref(v_vals_2222_);
lean_dec_ref(v_keys_2221_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___boxed(lean_object* v_x_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_){
_start:
{
size_t v_x_737__boxed_2232_; size_t v_x_738__boxed_2233_; lean_object* v_res_2234_; 
v_x_737__boxed_2232_ = lean_unbox_usize(v_x_2228_);
lean_dec(v_x_2228_);
v_x_738__boxed_2233_ = lean_unbox_usize(v_x_2229_);
lean_dec(v_x_2229_);
v_res_2234_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_2227_, v_x_737__boxed_2232_, v_x_738__boxed_2233_, v_x_2230_, v_x_2231_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(lean_object* v_x_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_){
_start:
{
uint64_t v___x_2238_; size_t v___x_2239_; size_t v___x_2240_; lean_object* v___x_2241_; 
v___x_2238_ = l_Lean_Expr_hash(v_x_2236_);
v___x_2239_ = lean_uint64_to_usize(v___x_2238_);
v___x_2240_ = ((size_t)1ULL);
v___x_2241_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_2235_, v___x_2239_, v___x_2240_, v_x_2236_, v_x_2237_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object* v_type_2242_, lean_object* v_inst_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v___x_2246_; lean_object* v_share_2247_; lean_object* v_maxFVar_2248_; lean_object* v_proofInstInfo_2249_; lean_object* v_proofInstInfoFVar_2250_; lean_object* v_inferType_2251_; lean_object* v_getLevel_2252_; lean_object* v_congrInfo_2253_; lean_object* v_defEqI_2254_; lean_object* v_extensions_2255_; lean_object* v_issues_2256_; lean_object* v_canon_2257_; lean_object* v_instanceOverrides_2258_; uint8_t v_debug_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2270_; 
v___x_2246_ = lean_st_ref_take(v_a_2244_);
v_share_2247_ = lean_ctor_get(v___x_2246_, 0);
v_maxFVar_2248_ = lean_ctor_get(v___x_2246_, 1);
v_proofInstInfo_2249_ = lean_ctor_get(v___x_2246_, 2);
v_proofInstInfoFVar_2250_ = lean_ctor_get(v___x_2246_, 3);
v_inferType_2251_ = lean_ctor_get(v___x_2246_, 4);
v_getLevel_2252_ = lean_ctor_get(v___x_2246_, 5);
v_congrInfo_2253_ = lean_ctor_get(v___x_2246_, 6);
v_defEqI_2254_ = lean_ctor_get(v___x_2246_, 7);
v_extensions_2255_ = lean_ctor_get(v___x_2246_, 8);
v_issues_2256_ = lean_ctor_get(v___x_2246_, 9);
v_canon_2257_ = lean_ctor_get(v___x_2246_, 10);
v_instanceOverrides_2258_ = lean_ctor_get(v___x_2246_, 11);
v_debug_2259_ = lean_ctor_get_uint8(v___x_2246_, sizeof(void*)*12);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2261_ = v___x_2246_;
v_isShared_2262_ = v_isSharedCheck_2270_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_instanceOverrides_2258_);
lean_inc(v_canon_2257_);
lean_inc(v_issues_2256_);
lean_inc(v_extensions_2255_);
lean_inc(v_defEqI_2254_);
lean_inc(v_congrInfo_2253_);
lean_inc(v_getLevel_2252_);
lean_inc(v_inferType_2251_);
lean_inc(v_proofInstInfoFVar_2250_);
lean_inc(v_proofInstInfo_2249_);
lean_inc(v_maxFVar_2248_);
lean_inc(v_share_2247_);
lean_dec(v___x_2246_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2270_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2263_ = lean_box(0);
v___x_2264_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(v_instanceOverrides_2258_, v_type_2242_, v_inst_2243_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 11, v___x_2264_);
v___x_2266_ = v___x_2261_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_share_2247_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_maxFVar_2248_);
lean_ctor_set(v_reuseFailAlloc_2269_, 2, v_proofInstInfo_2249_);
lean_ctor_set(v_reuseFailAlloc_2269_, 3, v_proofInstInfoFVar_2250_);
lean_ctor_set(v_reuseFailAlloc_2269_, 4, v_inferType_2251_);
lean_ctor_set(v_reuseFailAlloc_2269_, 5, v_getLevel_2252_);
lean_ctor_set(v_reuseFailAlloc_2269_, 6, v_congrInfo_2253_);
lean_ctor_set(v_reuseFailAlloc_2269_, 7, v_defEqI_2254_);
lean_ctor_set(v_reuseFailAlloc_2269_, 8, v_extensions_2255_);
lean_ctor_set(v_reuseFailAlloc_2269_, 9, v_issues_2256_);
lean_ctor_set(v_reuseFailAlloc_2269_, 10, v_canon_2257_);
lean_ctor_set(v_reuseFailAlloc_2269_, 11, v___x_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2269_, sizeof(void*)*12, v_debug_2259_);
v___x_2266_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_st_ref_put(v_a_2244_, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2263_);
return v___x_2268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___redArg___boxed(lean_object* v_type_2271_, lean_object* v_inst_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Meta_Sym_registerInstance___redArg(v_type_2271_, v_inst_2272_, v_a_2273_);
lean_dec(v_a_2273_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance(lean_object* v_type_2276_, lean_object* v_inst_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_Meta_Sym_registerInstance___redArg(v_type_2276_, v_inst_2277_, v_a_2279_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___boxed(lean_object* v_type_2286_, lean_object* v_inst_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Meta_Sym_registerInstance(v_type_2286_, v_inst_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0(lean_object* v_00_u03b2_2296_, lean_object* v_x_2297_, lean_object* v_x_2298_, lean_object* v_x_2299_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(v_x_2297_, v_x_2298_, v_x_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0(lean_object* v_00_u03b2_2301_, lean_object* v_x_2302_, size_t v_x_2303_, size_t v_x_2304_, lean_object* v_x_2305_, lean_object* v_x_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_2302_, v_x_2303_, v_x_2304_, v_x_2305_, v_x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2308_, lean_object* v_x_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_){
_start:
{
size_t v_x_943__boxed_2314_; size_t v_x_944__boxed_2315_; lean_object* v_res_2316_; 
v_x_943__boxed_2314_ = lean_unbox_usize(v_x_2310_);
lean_dec(v_x_2310_);
v_x_944__boxed_2315_ = lean_unbox_usize(v_x_2311_);
lean_dec(v_x_2311_);
v_res_2316_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0(v_00_u03b2_2308_, v_x_2309_, v_x_943__boxed_2314_, v_x_944__boxed_2315_, v_x_2312_, v_x_2313_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2317_, lean_object* v_n_2318_, lean_object* v_k_2319_, lean_object* v_v_2320_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(v_n_2318_, v_k_2319_, v_v_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2322_, size_t v_depth_2323_, lean_object* v_keys_2324_, lean_object* v_vals_2325_, lean_object* v_heq_2326_, lean_object* v_i_2327_, lean_object* v_entries_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_depth_2323_, v_keys_2324_, v_vals_2325_, v_i_2327_, v_entries_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2330_, lean_object* v_depth_2331_, lean_object* v_keys_2332_, lean_object* v_vals_2333_, lean_object* v_heq_2334_, lean_object* v_i_2335_, lean_object* v_entries_2336_){
_start:
{
size_t v_depth_boxed_2337_; lean_object* v_res_2338_; 
v_depth_boxed_2337_ = lean_unbox_usize(v_depth_2331_);
lean_dec(v_depth_2331_);
v_res_2338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2(v_00_u03b2_2330_, v_depth_boxed_2337_, v_keys_2332_, v_vals_2333_, v_heq_2334_, v_i_2335_, v_entries_2336_);
lean_dec_ref(v_vals_2333_);
lean_dec_ref(v_keys_2332_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2340_, v_x_2341_, v_x_2342_, v_x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2345_, lean_object* v_vals_2346_, lean_object* v_i_2347_, lean_object* v_k_2348_){
_start:
{
lean_object* v___x_2349_; uint8_t v___x_2350_; 
v___x_2349_ = lean_array_get_size(v_keys_2345_);
v___x_2350_ = lean_nat_dec_lt(v_i_2347_, v___x_2349_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; 
lean_dec(v_i_2347_);
v___x_2351_ = lean_box(0);
return v___x_2351_;
}
else
{
lean_object* v_k_x27_2352_; uint8_t v___x_2353_; 
v_k_x27_2352_ = lean_array_fget_borrowed(v_keys_2345_, v_i_2347_);
v___x_2353_ = lean_expr_eqv(v_k_2348_, v_k_x27_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = lean_nat_add(v_i_2347_, v___x_2354_);
lean_dec(v_i_2347_);
v_i_2347_ = v___x_2355_;
goto _start;
}
else
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_array_fget_borrowed(v_vals_2346_, v_i_2347_);
lean_dec(v_i_2347_);
lean_inc(v___x_2357_);
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
return v___x_2358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2359_, lean_object* v_vals_2360_, lean_object* v_i_2361_, lean_object* v_k_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2359_, v_vals_2360_, v_i_2361_, v_k_2362_);
lean_dec_ref(v_k_2362_);
lean_dec_ref(v_vals_2360_);
lean_dec_ref(v_keys_2359_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(lean_object* v_x_2364_, size_t v_x_2365_, lean_object* v_x_2366_){
_start:
{
if (lean_obj_tag(v_x_2364_) == 0)
{
lean_object* v_es_2367_; lean_object* v___x_2368_; size_t v___x_2369_; size_t v___x_2370_; lean_object* v_j_2371_; lean_object* v___x_2372_; 
v_es_2367_ = lean_ctor_get(v_x_2364_, 0);
v___x_2368_ = lean_box(2);
v___x_2369_ = ((size_t)31ULL);
v___x_2370_ = lean_usize_land(v_x_2365_, v___x_2369_);
v_j_2371_ = lean_usize_to_nat(v___x_2370_);
v___x_2372_ = lean_array_get_borrowed(v___x_2368_, v_es_2367_, v_j_2371_);
lean_dec(v_j_2371_);
switch(lean_obj_tag(v___x_2372_))
{
case 0:
{
lean_object* v_key_2373_; lean_object* v_val_2374_; uint8_t v___x_2375_; 
v_key_2373_ = lean_ctor_get(v___x_2372_, 0);
v_val_2374_ = lean_ctor_get(v___x_2372_, 1);
v___x_2375_ = lean_expr_eqv(v_x_2366_, v_key_2373_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_box(0);
return v___x_2376_;
}
else
{
lean_object* v___x_2377_; 
lean_inc(v_val_2374_);
v___x_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2377_, 0, v_val_2374_);
return v___x_2377_;
}
}
case 1:
{
lean_object* v_node_2378_; size_t v___x_2379_; size_t v___x_2380_; 
v_node_2378_ = lean_ctor_get(v___x_2372_, 0);
v___x_2379_ = ((size_t)5ULL);
v___x_2380_ = lean_usize_shift_right(v_x_2365_, v___x_2379_);
v_x_2364_ = v_node_2378_;
v_x_2365_ = v___x_2380_;
goto _start;
}
default: 
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_box(0);
return v___x_2382_;
}
}
}
else
{
lean_object* v_ks_2383_; lean_object* v_vs_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v_ks_2383_ = lean_ctor_get(v_x_2364_, 0);
v_vs_2384_ = lean_ctor_get(v_x_2364_, 1);
v___x_2385_ = lean_unsigned_to_nat(0u);
v___x_2386_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2383_, v_vs_2384_, v___x_2385_, v_x_2366_);
return v___x_2386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2387_, lean_object* v_x_2388_, lean_object* v_x_2389_){
_start:
{
size_t v_x_747__boxed_2390_; lean_object* v_res_2391_; 
v_x_747__boxed_2390_ = lean_unbox_usize(v_x_2388_);
lean_dec(v_x_2388_);
v_res_2391_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_2387_, v_x_747__boxed_2390_, v_x_2389_);
lean_dec_ref(v_x_2389_);
lean_dec_ref(v_x_2387_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(lean_object* v_x_2392_, lean_object* v_x_2393_){
_start:
{
uint64_t v___x_2394_; size_t v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = l_Lean_Expr_hash(v_x_2393_);
v___x_2395_ = lean_uint64_to_usize(v___x_2394_);
v___x_2396_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_2392_, v___x_2395_, v_x_2393_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg___boxed(lean_object* v_x_2397_, lean_object* v_x_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_x_2397_, v_x_2398_);
lean_dec_ref(v_x_2398_);
lean_dec_ref(v_x_2397_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object* v_type_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v___x_2407_; lean_object* v_instanceOverrides_2408_; lean_object* v___x_2409_; 
v___x_2407_ = lean_st_ref_get(v_a_2401_);
v_instanceOverrides_2408_ = lean_ctor_get(v___x_2407_, 11);
lean_inc_ref(v_instanceOverrides_2408_);
lean_dec(v___x_2407_);
v___x_2409_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_instanceOverrides_2408_, v_type_2400_);
lean_dec_ref(v_instanceOverrides_2408_);
if (lean_obj_tag(v___x_2409_) == 1)
{
lean_object* v___x_2410_; 
lean_dec_ref(v_type_2400_);
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
else
{
lean_object* v___x_2411_; 
lean_dec(v___x_2409_);
v___x_2411_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_2400_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
return v___x_2411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg___boxed(lean_object* v_type_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f(lean_object* v_type_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_2420_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___boxed(lean_object* v_type_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Meta_Sym_synthInstance_x3f(v_type_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0(lean_object* v_00_u03b2_2438_, lean_object* v_x_2439_, lean_object* v_x_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_x_2439_, v_x_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___boxed(lean_object* v_00_u03b2_2442_, lean_object* v_x_2443_, lean_object* v_x_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0(v_00_u03b2_2442_, v_x_2443_, v_x_2444_);
lean_dec_ref(v_x_2444_);
lean_dec_ref(v_x_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2446_, lean_object* v_x_2447_, size_t v_x_2448_, lean_object* v_x_2449_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_2447_, v_x_2448_, v_x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2451_, lean_object* v_x_2452_, lean_object* v_x_2453_, lean_object* v_x_2454_){
_start:
{
size_t v_x_831__boxed_2455_; lean_object* v_res_2456_; 
v_x_831__boxed_2455_ = lean_unbox_usize(v_x_2453_);
lean_dec(v_x_2453_);
v_res_2456_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0(v_00_u03b2_2451_, v_x_2452_, v_x_831__boxed_2455_, v_x_2454_);
lean_dec_ref(v_x_2454_);
lean_dec_ref(v_x_2452_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2457_, lean_object* v_keys_2458_, lean_object* v_vals_2459_, lean_object* v_heq_2460_, lean_object* v_i_2461_, lean_object* v_k_2462_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2458_, v_vals_2459_, v_i_2461_, v_k_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2464_, lean_object* v_keys_2465_, lean_object* v_vals_2466_, lean_object* v_heq_2467_, lean_object* v_i_2468_, lean_object* v_k_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2464_, v_keys_2465_, v_vals_2466_, v_heq_2467_, v_i_2468_, v_k_2469_);
lean_dec_ref(v_k_2469_);
lean_dec_ref(v_vals_2466_);
lean_dec_ref(v_keys_2465_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(lean_object* v_msgData_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; lean_object* v_env_2478_; uint8_t v___x_2479_; lean_object* v_env_2480_; lean_object* v___x_2481_; lean_object* v_toCold_2482_; lean_object* v_mctx_2483_; lean_object* v_lctx_2484_; lean_object* v_options_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2477_ = lean_st_ref_get(v___y_2475_);
v_env_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc_ref(v_env_2478_);
lean_dec(v___x_2477_);
v___x_2479_ = 0;
v_env_2480_ = l_Lean_Environment_setRecordingDeps(v_env_2478_, v___x_2479_);
v___x_2481_ = lean_st_ref_get(v___y_2473_);
v_toCold_2482_ = lean_ctor_get(v___y_2474_, 0);
v_mctx_2483_ = lean_ctor_get(v___x_2481_, 0);
lean_inc_ref(v_mctx_2483_);
lean_dec(v___x_2481_);
v_lctx_2484_ = lean_ctor_get(v___y_2472_, 2);
v_options_2485_ = lean_ctor_get(v_toCold_2482_, 2);
lean_inc_ref(v_options_2485_);
lean_inc_ref(v_lctx_2484_);
v___x_2486_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2486_, 0, v_env_2480_);
lean_ctor_set(v___x_2486_, 1, v_mctx_2483_);
lean_ctor_set(v___x_2486_, 2, v_lctx_2484_);
lean_ctor_set(v___x_2486_, 3, v_options_2485_);
v___x_2487_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
lean_ctor_set(v___x_2487_, 1, v_msgData_2471_);
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0___boxed(lean_object* v_msgData_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(v_msgData_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(lean_object* v_msg_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_ref_2502_; lean_object* v___x_2503_; lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2512_; 
v_ref_2502_ = lean_ctor_get(v___y_2499_, 2);
v___x_2503_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(v_msg_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2506_ = v___x_2503_;
v_isShared_2507_ = v_isSharedCheck_2512_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2512_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
lean_inc(v_ref_2502_);
v___x_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2508_, 0, v_ref_2502_);
lean_ctor_set(v___x_2508_, 1, v_a_2504_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set_tag(v___x_2506_, 1);
lean_ctor_set(v___x_2506_, 0, v___x_2508_);
v___x_2510_ = v___x_2506_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg___boxed(lean_object* v_msg_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v_msg_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
return v_res_2519_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_synthInstance___closed__1(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = ((lean_object*)(l_Lean_Meta_Sym_synthInstance___closed__0));
v___x_2522_ = l_Lean_stringToMessageData(v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance(lean_object* v_type_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v___x_2531_; 
lean_inc_ref(v_type_2523_);
v___x_2531_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_2523_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2544_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2544_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2544_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
if (lean_obj_tag(v_a_2532_) == 1)
{
lean_object* v_val_2536_; lean_object* v___x_2538_; 
lean_dec_ref(v_type_2523_);
v_val_2536_ = lean_ctor_get(v_a_2532_, 0);
lean_inc(v_val_2536_);
lean_dec_ref_known(v_a_2532_, 1);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v_val_2536_);
v___x_2538_ = v___x_2534_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_val_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
else
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_del_object(v___x_2534_);
lean_dec(v_a_2532_);
v___x_2540_ = lean_obj_once(&l_Lean_Meta_Sym_synthInstance___closed__1, &l_Lean_Meta_Sym_synthInstance___closed__1_once, _init_l_Lean_Meta_Sym_synthInstance___closed__1);
v___x_2541_ = l_Lean_indentExpr(v_type_2523_);
v___x_2542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2540_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v___x_2542_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
return v___x_2543_;
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v_type_2523_);
v_a_2545_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2531_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2531_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance___boxed(lean_object* v_type_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_Meta_Sym_synthInstance(v_type_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0(lean_object* v_00_u03b1_2562_, lean_object* v_msg_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v_msg_2563_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___boxed(lean_object* v_00_u03b1_2572_, lean_object* v_msg_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0(v_00_u03b1_2572_, v_msg_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(lean_object* v_x_2582_, lean_object* v_type_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2602_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2602_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2602_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
if (lean_obj_tag(v_a_2591_) == 1)
{
lean_object* v_val_2595_; lean_object* v___x_2596_; 
lean_del_object(v___x_2593_);
v_val_2595_ = lean_ctor_get(v_a_2591_, 0);
lean_inc(v_val_2595_);
lean_dec_ref_known(v_a_2591_, 1);
v___x_2596_ = l_Lean_Meta_isExprDefEq(v_x_2582_, v_val_2595_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
return v___x_2596_;
}
else
{
uint8_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
lean_dec(v_a_2591_);
lean_dec_ref(v_x_2582_);
v___x_2597_ = 0;
v___x_2598_ = lean_box(v___x_2597_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2598_);
v___x_2600_ = v___x_2593_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec_ref(v_x_2582_);
v_a_2603_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2590_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2590_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg___boxed(lean_object* v_x_2611_, lean_object* v_type_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_x_2611_, v_type_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec(v_a_2613_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign(lean_object* v_x_2620_, lean_object* v_type_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_x_2620_, v_type_2621_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___boxed(lean_object* v_x_2630_, lean_object* v_type_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_Lean_Meta_Sym_synthInstanceAndAssign(v_x_2630_, v_type_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
return v_res_2639_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* runtime_initialize_Init_GrindInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Int(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Package(uint8_t builtin);
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
res = runtime_initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ordered_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ordered_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts = _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts();
lean_mark_persistent(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts);
l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts = _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts();
lean_mark_persistent(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInsts);
l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring = _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring();
lean_mark_persistent(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring);
l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring = _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring();
lean_mark_persistent(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring);
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
lean_object* initialize_Init_Grind_Ring(uint8_t builtin);
lean_object* initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* initialize_Init_GrindInstances(uint8_t builtin);
lean_object* initialize_Init_Grind_Ordered_Int(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Package(uint8_t builtin);
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
res = initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Package(builtin);
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
