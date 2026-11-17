// Lean compiler output
// Module: Lean.Meta.Sym.SynthInstance
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.SynthInstance import Init.Grind.Ring import Init.Grind.Ordered.Ring import Init.GrindInstances import Init.Grind.Ordered.Int import Init.Data.Int.Package import Lean.CoreM
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHMul;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstAdd;
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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isDefEqStuckExceptionId;
lean_object* l_Lean_Meta_synthInstanceCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_Nat_mkInstHAdd;
extern lean_object* l_Lean_Nat_mkInstHSub;
extern lean_object* l_Lean_Nat_mkInstHDiv;
extern lean_object* l_Lean_Nat_mkInstHMod;
extern lean_object* l_Lean_Nat_mkInstHPow;
extern lean_object* l_Lean_Nat_mkInstSub;
extern lean_object* l_Lean_Nat_mkInstMul;
extern lean_object* l_Lean_Nat_mkInstDiv;
extern lean_object* l_Lean_Nat_mkInstMod;
extern lean_object* l_Lean_Nat_mkInstPow;
extern lean_object* l_Lean_Nat_mkInstNatPow;
extern lean_object* l_Lean_Nat_mkInstLT;
extern lean_object* l_Lean_Nat_mkInstLE;
extern lean_object* l_Lean_Int_mkInstHAdd;
extern lean_object* l_Lean_Int_mkInstHSub;
extern lean_object* l_Lean_Int_mkInstHMul;
extern lean_object* l_Lean_Int_mkInstHDiv;
extern lean_object* l_Lean_Int_mkInstHMod;
extern lean_object* l_Lean_Int_mkInstHPow;
extern lean_object* l_Lean_Int_mkInstAdd;
extern lean_object* l_Lean_Int_mkInstSub;
extern lean_object* l_Lean_Int_mkInstMul;
extern lean_object* l_Lean_Int_mkInstDiv;
extern lean_object* l_Lean_Int_mkInstMod;
extern lean_object* l_Lean_Int_mkInstPowNat;
extern lean_object* l_Lean_Int_mkInstPow;
extern lean_object* l_Lean_Int_mkInstNeg;
extern lean_object* l_Lean_Int_mkInstLT;
extern lean_object* l_Lean_Int_mkInstLE;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__33 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__33_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__34 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__34_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__38;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__39;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sub"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__40 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__40_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__40_value),LEAN_SCALAR_PTR_LITERAL(203, 50, 219, 228, 204, 142, 182, 246)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__41 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__41_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__43;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__44;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mul"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__45 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__45_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__45_value),LEAN_SCALAR_PTR_LITERAL(155, 25, 183, 66, 31, 85, 84, 65)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__46 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__46_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__48;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__49;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Div"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__50 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__50_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__50_value),LEAN_SCALAR_PTR_LITERAL(153, 247, 56, 19, 64, 245, 190, 87)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__51 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__51_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__52;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__53;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__54;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mod"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__55 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__55_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__55_value),LEAN_SCALAR_PTR_LITERAL(141, 157, 192, 123, 66, 123, 34, 2)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__56 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__56_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__57;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__58;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__59;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Pow"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__60 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__60_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__60_value),LEAN_SCALAR_PTR_LITERAL(237, 192, 51, 134, 187, 116, 61, 36)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__61 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__61_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__62;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__63;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__64;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__65;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "NatPow"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__66 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__66_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__66_value),LEAN_SCALAR_PTR_LITERAL(36, 252, 247, 75, 236, 16, 44, 32)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__67 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__67_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__68;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__69;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__70;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__71 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__71_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__71_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__72 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__72_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__73 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__73_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__73_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__74 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__74_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__75;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__76;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__77;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__78;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__79_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__79;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__80;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__81_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__81;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__82;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__83;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__84;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__85_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__85;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__86;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__87;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__88;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__89_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__89;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__90_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__90;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__91_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__91;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__92_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__92;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__93_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__93;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__94_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__94;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__95_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__95;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__96_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__96;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__97_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__97;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__98_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__98;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__99_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__99;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__100_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__100;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__101 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__101_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__101_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__102 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__102_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__103_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__103;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__104_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__104;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__105_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__105;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__106_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__106;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__107_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__107;
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
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTNat"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(141, 27, 201, 217, 48, 203, 85, 203)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decLt"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 116, 195, 81, 41, 93, 3, 179)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLENat"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(211, 47, 64, 46, 87, 101, 57, 105)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__8_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decLe"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(222, 181, 165, 207, 140, 26, 31, 233)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__11;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__13_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__15_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instOfNatNat"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(217, 8, 172, 44, 179, 254, 147, 95)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__19 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__20;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__21 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 253, 199, 38, 151, 242, 146)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__22 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__23;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__24 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__25 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__25_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__26 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__71_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__26_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__27_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__28 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__73_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__29_value;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLEInt"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__30_value),LEAN_SCALAR_PTR_LITERAL(190, 143, 147, 243, 104, 145, 221, 241)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__32_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(64, 211, 213, 110, 61, 40, 149, 63)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__32 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__32_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__33;
static const lean_string_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTInt"};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__34 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__34_value),LEAN_SCALAR_PTR_LITERAL(174, 212, 102, 196, 69, 170, 149, 126)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__36_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(168, 105, 33, 134, 172, 206, 181, 195)}};
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
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__42_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__41_value),LEAN_SCALAR_PTR_LITERAL(3, 193, 133, 18, 69, 57, 20, 76)}};
static const lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__42 = (const lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__42_value;
static lean_once_cell_t l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__43;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__0;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "instCommRingInt"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 31, 43, 123, 13, 223, 116, 234)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__5;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__6_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__7_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__11;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__12_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__13_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__16;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toCommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__6_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__17_value),LEAN_SCALAR_PTR_LITERAL(134, 95, 181, 253, 18, 104, 213, 131)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__19;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__20 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "toNatModule"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__21 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__20_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__21_value),LEAN_SCALAR_PTR_LITERAL(156, 107, 255, 119, 73, 35, 26, 237)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__22 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__23 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__23_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__13_value),LEAN_SCALAR_PTR_LITERAL(134, 3, 13, 60, 96, 160, 201, 59)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__24 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__24_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__25;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__26;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__27;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__28;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "instLinearOrderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__29 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__29_value),LEAN_SCALAR_PTR_LITERAL(131, 14, 207, 248, 19, 164, 92, 69)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__30 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__30_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__31;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LinearOrderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__33 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__33_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "toLinearPreorderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__34 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__34_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__35_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__33_value),LEAN_SCALAR_PTR_LITERAL(234, 23, 176, 82, 70, 91, 79, 141)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__35_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__34_value),LEAN_SCALAR_PTR_LITERAL(49, 11, 127, 82, 11, 218, 43, 122)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__35 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__35_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__36;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__37;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "PreorderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__38 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__38_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toIsPreorder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__39 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__39_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__40_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__38_value),LEAN_SCALAR_PTR_LITERAL(213, 46, 53, 169, 1, 182, 53, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__40_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__39_value),LEAN_SCALAR_PTR_LITERAL(102, 251, 239, 168, 167, 218, 99, 248)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__40 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__40_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "LinearPreorderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__41 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__41_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "toPreorderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__42 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__42_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__43_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__41_value),LEAN_SCALAR_PTR_LITERAL(225, 122, 95, 75, 156, 33, 23, 202)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__43_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__42_value),LEAN_SCALAR_PTR_LITERAL(220, 190, 227, 44, 91, 141, 117, 87)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__43 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__43_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__44;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__45;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__46;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__47;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__48;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__49;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instCommSemiringNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__50 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__50_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__51_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__51_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__50_value),LEAN_SCALAR_PTR_LITERAL(40, 222, 188, 237, 59, 115, 167, 190)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__51 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__51_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__52;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__54;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__55;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__56;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__57;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__59;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instIsPreorderNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__60 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__60_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__61_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__61_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__60_value),LEAN_SCALAR_PTR_LITERAL(82, 153, 165, 139, 213, 168, 248, 23)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__61 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__61_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__62;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instIsLinearOrder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__63 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__63_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__64_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__63_value),LEAN_SCALAR_PTR_LITERAL(65, 94, 2, 50, 92, 94, 216, 236)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__64 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__64_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__65;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__66 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__66_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__66_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__67 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__67_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__69;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDvd"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__70 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__70_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__71_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__70_value),LEAN_SCALAR_PTR_LITERAL(154, 210, 229, 77, 176, 177, 112, 145)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__71 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__71_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__72;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__73;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__74;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__75_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__75_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__6_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__75 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__75_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__77;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__78;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__79_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__79_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__12_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__79 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__79_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__80;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__81_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__81;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__82_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__82_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__23_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__82 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__82_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__83;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__84;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__85_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__85_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__85_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__20_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__85 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__85_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__86;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__87;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__88;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__89_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__89;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__90_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__90;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__91_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__91;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__92_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__92;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "IsLinearOrder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__93 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__93_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__94_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__93_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__94 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__94_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__95_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__95;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__96_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__96;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LawfulOrderLT"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__97 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__97_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__98_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__97_value),LEAN_SCALAR_PTR_LITERAL(125, 54, 67, 105, 183, 31, 31, 114)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__98 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__98_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__99_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__99;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__100_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__100;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__101;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "instLawfulOrderLTNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__102 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__102_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__103_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__103_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__103_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__102_value),LEAN_SCALAR_PTR_LITERAL(67, 147, 221, 102, 44, 68, 100, 197)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__103 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__103_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__104_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__104;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__105_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__105;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OrderedRing"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__106 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__106_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__107_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__107_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__107_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__107_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__106_value),LEAN_SCALAR_PTR_LITERAL(245, 123, 155, 51, 122, 17, 247, 247)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__107 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__107_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__108;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__109_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__109;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instOrderedRingNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__110 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__110_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__111_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__111_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__111_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__110_value),LEAN_SCALAR_PTR_LITERAL(151, 152, 80, 183, 84, 69, 75, 40)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__111 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__111_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__112_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__112;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__113_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__113;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__114_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__114;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__115 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__115_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__115_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__116 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__116_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__117_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__117;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__118 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__118_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__118_value),LEAN_SCALAR_PTR_LITERAL(164, 225, 253, 29, 29, 200, 99, 105)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__119 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__119_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__120_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__120;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__121_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__121;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__122_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__122;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Max"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__123 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__123_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__123_value),LEAN_SCALAR_PTR_LITERAL(169, 95, 226, 81, 206, 208, 89, 76)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__124 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__124_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__125_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__125;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instMax"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__126 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__126_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__127_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__127_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__126_value),LEAN_SCALAR_PTR_LITERAL(98, 227, 45, 92, 47, 209, 226, 196)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__127 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__127_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__128_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__128;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__129_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__129;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__130_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__130;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__131_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__131;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__132_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__132;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__133_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__133;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NatModule"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__134 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__134_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__135_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__135_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__135_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__135_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__134_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 171, 186, 15, 174, 251, 179)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__135 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__135_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__136_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__136;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__137_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__137;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__138_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__138;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NoNatZeroDivisors"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__139 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__139_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__140_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__140_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__140_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__140_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__139_value),LEAN_SCALAR_PTR_LITERAL(78, 29, 6, 12, 7, 77, 98, 78)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__140 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__140_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__141_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__141;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__142_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__142;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "instNoNatZeroDivisorsNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__143 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__143_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__144_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__144_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__144_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__144_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__143_value),LEAN_SCALAR_PTR_LITERAL(80, 62, 83, 18, 35, 229, 169, 162)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__144 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__144_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__145_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__145;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__146_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__146;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__147_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__147;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "IsPreorder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__148 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__148_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__149_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__149_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__148_value),LEAN_SCALAR_PTR_LITERAL(184, 213, 76, 156, 147, 68, 250, 139)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__149 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__149_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__150_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__150;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "IsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__151 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__151_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__152_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__152_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__151_value),LEAN_SCALAR_PTR_LITERAL(196, 84, 36, 174, 137, 182, 135, 55)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__152 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__152_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "toIsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__153 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__153_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__154_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__154_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__154_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__93_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__154_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__153_value),LEAN_SCALAR_PTR_LITERAL(83, 108, 214, 71, 226, 119, 72, 107)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__154 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__154_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__155_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__155;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__156_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__156;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "IsLinearPreorder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__157 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__157_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__158_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__158_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__157_value),LEAN_SCALAR_PTR_LITERAL(149, 98, 195, 196, 59, 47, 77, 198)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__158 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__158_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "toIsLinearPreorder"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__159 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__159_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__160_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__160_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__160_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__93_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__160_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__159_value),LEAN_SCALAR_PTR_LITERAL(222, 35, 97, 11, 70, 227, 118, 244)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__160 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__160_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__161 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__161_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__162_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__162_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__162_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__162_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__161_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__162 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__162_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__163_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__163;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__164_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__164;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__165_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__165;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__166_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__166;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__167_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__167;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__168_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__168;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__169_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__169;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__170_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__170;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__171 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__171_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__172_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__172_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__172_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__172_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__171_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__172 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__172_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__173_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instAddNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__173 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__173_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__173_value),LEAN_SCALAR_PTR_LITERAL(228, 164, 175, 25, 228, 165, 175, 183)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__174 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__174_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__175_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__175;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__176_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__176;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__177_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__177;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "instAddRightCancelNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__178 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__178_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__179_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__179_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__179_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__179_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__178_value),LEAN_SCALAR_PTR_LITERAL(61, 59, 84, 219, 165, 123, 148, 70)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__179 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__179_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__180_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__180;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__181_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__181;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__182_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__182;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__184_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__184;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__185 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__185_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__185_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__186 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__186_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__187_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__187;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__188_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__188;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__189_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__189;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__190_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__190;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__191_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__191_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__191_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__126_value),LEAN_SCALAR_PTR_LITERAL(172, 71, 86, 64, 121, 239, 29, 46)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__191 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__191_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__192_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__192;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__193_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__193;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__194_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__194;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__195_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__195;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__196_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__196_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__70_value),LEAN_SCALAR_PTR_LITERAL(164, 20, 243, 72, 185, 226, 91, 120)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__196 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__196_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__197_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__197;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__198_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__198;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__199_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__199;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__200_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__200;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__201_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__201;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__202_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__202;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__203_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__203;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__204_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__204;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__205_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__205_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__205_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__41_value),LEAN_SCALAR_PTR_LITERAL(225, 122, 95, 75, 156, 33, 23, 202)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__205_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__205_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__159_value),LEAN_SCALAR_PTR_LITERAL(136, 249, 219, 90, 192, 97, 192, 138)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__205 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__205_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__206_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__206;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__207_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__207;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__208_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "instIsLinearOrderInt"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__208 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__208_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__209_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__209_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__209_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__209_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__209_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__208_value),LEAN_SCALAR_PTR_LITERAL(131, 250, 55, 79, 188, 53, 20, 57)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__209 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__209_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__210_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__210;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__211_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__211;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__212_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__212;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__213_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "instLawfulOrderLTInt"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__213 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__213_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__214_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__214_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__214_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__214_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__214_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__213_value),LEAN_SCALAR_PTR_LITERAL(15, 49, 64, 177, 151, 67, 90, 197)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__214 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__214_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__215_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__215;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__216_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__216;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__217_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__217;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__218_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__218;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__219_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instOrderedRingInt"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__219 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__219_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__220_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__220_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__220_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__220_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__220_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__219_value),LEAN_SCALAR_PTR_LITERAL(39, 57, 139, 49, 47, 134, 165, 10)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__220 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__220_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__221_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__221;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__222_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__222;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__223_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__223;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__224_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__224;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__225_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__225;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__226_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__226;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__227_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__227;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__228_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__228;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__229_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__229;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__230_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__230;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__231_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "instNoNatZeroDivisorsInt"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__231 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__231_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__232_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__232_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__232_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__232_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__232_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__231_value),LEAN_SCALAR_PTR_LITERAL(78, 244, 183, 128, 140, 77, 95, 233)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__232 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__232_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__233_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__233;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__234_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__234;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__235_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__235;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__236_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__236;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__237_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "PartialOrderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__237 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__237_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__238_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__238_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__238_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__237_value),LEAN_SCALAR_PTR_LITERAL(161, 83, 12, 138, 219, 25, 15, 147)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__238_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__238_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__153_value),LEAN_SCALAR_PTR_LITERAL(189, 36, 219, 76, 135, 177, 227, 44)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__238 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__238_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__239_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "toPartialOrderPackage"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__239 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__239_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__240_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__32_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__240_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__240_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__33_value),LEAN_SCALAR_PTR_LITERAL(234, 23, 176, 82, 70, 91, 79, 141)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__240_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__240_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__239_value),LEAN_SCALAR_PTR_LITERAL(104, 50, 28, 184, 150, 106, 140, 110)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__240 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__240_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__241_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__241;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__242_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__242;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__243_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__243;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__244_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__244;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__245_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__245;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__246_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__246;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__247_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__247;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__248_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__248;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__249_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__249;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__250_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__250;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__251_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__251;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__252_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__252;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__253_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__253;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__254_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__254;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__255_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__255;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__256_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__256;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsTypeCarrier___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsTypeCarrier___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsTypeCarrier;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsSortCarrier___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsSortCarrier___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsSortCarrier;
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
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 166, 196, 137, 32, 118, 33, 172)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IsCharP"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 211, 245, 119, 67, 24, 212, 73)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instIsCharPNatOfNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(184, 168, 68, 32, 159, 176, 186, 43)}};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__7;
static const lean_string_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "instIsCharPIntOfNatNat"};
static const lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
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
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_nbuckets_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_42_ = lean_array_get_size(v_data_41_);
v___x_43_ = lean_unsigned_to_nat(2u);
v_nbuckets_44_ = lean_nat_mul(v___x_42_, v___x_43_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_box(0);
v___x_47_ = lean_mk_array(v_nbuckets_44_, v___x_46_);
v___x_48_ = lean_array_propagate_mark(v_data_41_, v___x_47_);
v___x_49_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3___redArg(v___x_45_, v_data_41_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___redArg(lean_object* v_a_50_, lean_object* v_x_51_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_57_, lean_object* v_x_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___redArg(v_a_57_, v_x_58_);
lean_dec(v_x_58_);
lean_dec_ref(v_a_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__3___redArg(lean_object* v_a_61_, lean_object* v_b_62_, lean_object* v_x_63_){
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
v___x_71_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__3___redArg(v_a_61_, v_b_62_, v_tail_66_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0___redArg(lean_object* v_m_79_, lean_object* v_a_80_, lean_object* v_b_81_){
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
v___x_101_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___redArg(v_a_80_, v_bkt_100_);
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
v_val_112_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2___redArg(v_buckets_x27_105_);
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
v___x_121_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__3___redArg(v_a_80_, v_b_81_, v_bkt_100_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg(lean_object* v_as_x27_127_, lean_object* v_b_128_){
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
v_r_133_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0___redArg(v_b_128_, v_fst_131_, v_snd_132_);
v_as_x27_127_ = v_tail_130_;
v_b_128_ = v_r_133_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_135_, lean_object* v_b_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg(v_as_x27_135_, v_b_136_);
lean_dec(v_as_x27_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0(lean_object* v_m_138_, lean_object* v_l_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg(v_l_139_, v_m_138_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0___boxed(lean_object* v_m_141_, lean_object* v_l_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0(v_m_141_, v_l_142_);
lean_dec(v_l_142_);
return v_res_143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5(void){
_start:
{
lean_object* v_us_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_us_156_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2));
v___x_157_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__4));
v___x_158_ = l_Lean_mkConst(v___x_157_, v_us_156_);
return v___x_158_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__6(void){
_start:
{
lean_object* v_nat_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_nat_159_ = l_Lean_Nat_mkType;
v___x_160_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5);
v___x_161_ = l_Lean_mkApp3(v___x_160_, v_nat_159_, v_nat_159_, v_nat_159_);
return v___x_161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__7(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = l_Lean_Nat_mkInstHAdd;
v___x_163_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__6, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__6_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__6);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
return v___x_164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10(void){
_start:
{
lean_object* v_us_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_us_168_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2));
v___x_169_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__9));
v___x_170_ = l_Lean_mkConst(v___x_169_, v_us_168_);
return v___x_170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__11(void){
_start:
{
lean_object* v_nat_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_nat_171_ = l_Lean_Nat_mkType;
v___x_172_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10);
v___x_173_ = l_Lean_mkApp3(v___x_172_, v_nat_171_, v_nat_171_, v_nat_171_);
return v___x_173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__12(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = l_Lean_Nat_mkInstHSub;
v___x_175_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__11, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__11_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__11);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15(void){
_start:
{
lean_object* v_us_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_us_180_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2));
v___x_181_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__14));
v___x_182_ = l_Lean_mkConst(v___x_181_, v_us_180_);
return v___x_182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__16(void){
_start:
{
lean_object* v_nat_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_nat_183_ = l_Lean_Nat_mkType;
v___x_184_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15);
v___x_185_ = l_Lean_mkApp3(v___x_184_, v_nat_183_, v_nat_183_, v_nat_183_);
return v___x_185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__17(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = l_Lean_Nat_mkInstHMul;
v___x_187_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__16, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__16_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__16);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20(void){
_start:
{
lean_object* v_us_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_us_192_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2));
v___x_193_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__19));
v___x_194_ = l_Lean_mkConst(v___x_193_, v_us_192_);
return v___x_194_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__21(void){
_start:
{
lean_object* v_nat_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_nat_195_ = l_Lean_Nat_mkType;
v___x_196_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20);
v___x_197_ = l_Lean_mkApp3(v___x_196_, v_nat_195_, v_nat_195_, v_nat_195_);
return v___x_197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__22(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = l_Lean_Nat_mkInstHDiv;
v___x_199_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__21, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__21_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__21);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25(void){
_start:
{
lean_object* v_us_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_us_204_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2));
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__24));
v___x_206_ = l_Lean_mkConst(v___x_205_, v_us_204_);
return v___x_206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__26(void){
_start:
{
lean_object* v_nat_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_nat_207_ = l_Lean_Nat_mkType;
v___x_208_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25);
v___x_209_ = l_Lean_mkApp3(v___x_208_, v_nat_207_, v_nat_207_, v_nat_207_);
return v___x_209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__27(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = l_Lean_Nat_mkInstHMod;
v___x_211_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__26, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__26_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__26);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
return v___x_212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30(void){
_start:
{
lean_object* v_us_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_us_216_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__2));
v___x_217_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__29));
v___x_218_ = l_Lean_mkConst(v___x_217_, v_us_216_);
return v___x_218_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__31(void){
_start:
{
lean_object* v_nat_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_nat_219_ = l_Lean_Nat_mkType;
v___x_220_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30);
v___x_221_ = l_Lean_mkApp3(v___x_220_, v_nat_219_, v_nat_219_, v_nat_219_);
return v___x_221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__32(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = l_Lean_Nat_mkInstHPow;
v___x_223_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__31, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__31_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__31);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = l_Lean_Level_ofNat(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_box(0);
v___x_231_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35);
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36);
v___x_234_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__34));
v___x_235_ = l_Lean_mkConst(v___x_234_, v___x_233_);
return v___x_235_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__38(void){
_start:
{
lean_object* v_nat_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_nat_236_ = l_Lean_Nat_mkType;
v___x_237_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37);
v___x_238_ = l_Lean_Expr_app___override(v___x_237_, v_nat_236_);
return v___x_238_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__39(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = l_Lean_Nat_mkInstAdd;
v___x_240_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__38, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__38_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__38);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36);
v___x_246_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__41));
v___x_247_ = l_Lean_mkConst(v___x_246_, v___x_245_);
return v___x_247_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__43(void){
_start:
{
lean_object* v_nat_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_nat_248_ = l_Lean_Nat_mkType;
v___x_249_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42);
v___x_250_ = l_Lean_Expr_app___override(v___x_249_, v_nat_248_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__44(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = l_Lean_Nat_mkInstSub;
v___x_252_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__43, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__43_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__43);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36);
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__46));
v___x_259_ = l_Lean_mkConst(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__48(void){
_start:
{
lean_object* v_nat_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_nat_260_ = l_Lean_Nat_mkType;
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47);
v___x_262_ = l_Lean_Expr_app___override(v___x_261_, v_nat_260_);
return v___x_262_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__49(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = l_Lean_Nat_mkInstMul;
v___x_264_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__48, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__48_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__48);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__52(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36);
v___x_270_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__51));
v___x_271_ = l_Lean_mkConst(v___x_270_, v___x_269_);
return v___x_271_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__53(void){
_start:
{
lean_object* v_nat_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_nat_272_ = l_Lean_Nat_mkType;
v___x_273_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__52, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__52_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__52);
v___x_274_ = l_Lean_Expr_app___override(v___x_273_, v_nat_272_);
return v___x_274_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__54(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = l_Lean_Nat_mkInstDiv;
v___x_276_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__53, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__53_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__53);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__57(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36);
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__56));
v___x_283_ = l_Lean_mkConst(v___x_282_, v___x_281_);
return v___x_283_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__58(void){
_start:
{
lean_object* v_nat_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_nat_284_ = l_Lean_Nat_mkType;
v___x_285_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__57, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__57_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__57);
v___x_286_ = l_Lean_Expr_app___override(v___x_285_, v_nat_284_);
return v___x_286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__59(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = l_Lean_Nat_mkInstMod;
v___x_288_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__58, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__58_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__58);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__62(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36);
v___x_294_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35);
v___x_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__63(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__62, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__62_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__62);
v___x_297_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__61));
v___x_298_ = l_Lean_mkConst(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__64(void){
_start:
{
lean_object* v_nat_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_nat_299_ = l_Lean_Nat_mkType;
v___x_300_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__63, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__63_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__63);
v___x_301_ = l_Lean_mkAppB(v___x_300_, v_nat_299_, v_nat_299_);
return v___x_301_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__65(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = l_Lean_Nat_mkInstPow;
v___x_303_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__64, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__64_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__64);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
return v___x_304_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__68(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36);
v___x_309_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__67));
v___x_310_ = l_Lean_mkConst(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__69(void){
_start:
{
lean_object* v_nat_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_nat_311_ = l_Lean_Nat_mkType;
v___x_312_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__68);
v___x_313_ = l_Lean_Expr_app___override(v___x_312_, v_nat_311_);
return v___x_313_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__70(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = l_Lean_Nat_mkInstNatPow;
v___x_315_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__69, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__69_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__69);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__75(void){
_start:
{
lean_object* v_int_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_int_323_ = l_Lean_Int_mkType;
v___x_324_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__5);
v___x_325_ = l_Lean_mkApp3(v___x_324_, v_int_323_, v_int_323_, v_int_323_);
return v___x_325_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__76(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = l_Lean_Int_mkInstHAdd;
v___x_327_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__75, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__75_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__75);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
return v___x_328_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__77(void){
_start:
{
lean_object* v_int_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_int_329_ = l_Lean_Int_mkType;
v___x_330_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__10);
v___x_331_ = l_Lean_mkApp3(v___x_330_, v_int_329_, v_int_329_, v_int_329_);
return v___x_331_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__78(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = l_Lean_Int_mkInstHSub;
v___x_333_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__77, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__77_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__77);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_332_);
return v___x_334_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__79(void){
_start:
{
lean_object* v_int_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_int_335_ = l_Lean_Int_mkType;
v___x_336_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__15);
v___x_337_ = l_Lean_mkApp3(v___x_336_, v_int_335_, v_int_335_, v_int_335_);
return v___x_337_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__80(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = l_Lean_Int_mkInstHMul;
v___x_339_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__79, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__79_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__79);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_338_);
return v___x_340_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__81(void){
_start:
{
lean_object* v_int_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_int_341_ = l_Lean_Int_mkType;
v___x_342_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__20);
v___x_343_ = l_Lean_mkApp3(v___x_342_, v_int_341_, v_int_341_, v_int_341_);
return v___x_343_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__82(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = l_Lean_Int_mkInstHDiv;
v___x_345_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__81, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__81_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__81);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__83(void){
_start:
{
lean_object* v_int_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_int_347_ = l_Lean_Int_mkType;
v___x_348_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__25);
v___x_349_ = l_Lean_mkApp3(v___x_348_, v_int_347_, v_int_347_, v_int_347_);
return v___x_349_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__84(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = l_Lean_Int_mkInstHMod;
v___x_351_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__83, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__83_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__83);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_350_);
return v___x_352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__85(void){
_start:
{
lean_object* v_nat_353_; lean_object* v_int_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_nat_353_ = l_Lean_Nat_mkType;
v_int_354_ = l_Lean_Int_mkType;
v___x_355_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__30);
v___x_356_ = l_Lean_mkApp3(v___x_355_, v_int_354_, v_nat_353_, v_int_354_);
return v___x_356_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__86(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = l_Lean_Int_mkInstHPow;
v___x_358_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__85, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__85_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__85);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___x_357_);
return v___x_359_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__87(void){
_start:
{
lean_object* v_int_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_int_360_ = l_Lean_Int_mkType;
v___x_361_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__37);
v___x_362_ = l_Lean_Expr_app___override(v___x_361_, v_int_360_);
return v___x_362_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__88(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = l_Lean_Int_mkInstAdd;
v___x_364_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__87, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__87_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__87);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
return v___x_365_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__89(void){
_start:
{
lean_object* v_int_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_int_366_ = l_Lean_Int_mkType;
v___x_367_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__42);
v___x_368_ = l_Lean_Expr_app___override(v___x_367_, v_int_366_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__90(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = l_Lean_Int_mkInstSub;
v___x_370_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__89, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__89_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__89);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__91(void){
_start:
{
lean_object* v_int_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_int_372_ = l_Lean_Int_mkType;
v___x_373_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__47);
v___x_374_ = l_Lean_Expr_app___override(v___x_373_, v_int_372_);
return v___x_374_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__92(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = l_Lean_Int_mkInstMul;
v___x_376_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__91, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__91_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__91);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__93(void){
_start:
{
lean_object* v_int_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_int_378_ = l_Lean_Int_mkType;
v___x_379_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__52, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__52_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__52);
v___x_380_ = l_Lean_Expr_app___override(v___x_379_, v_int_378_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__94(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = l_Lean_Int_mkInstDiv;
v___x_382_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__93, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__93_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__93);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
return v___x_383_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__95(void){
_start:
{
lean_object* v_int_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_int_384_ = l_Lean_Int_mkType;
v___x_385_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__57, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__57_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__57);
v___x_386_ = l_Lean_Expr_app___override(v___x_385_, v_int_384_);
return v___x_386_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__96(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = l_Lean_Int_mkInstMod;
v___x_388_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__95, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__95_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__95);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_387_);
return v___x_389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__97(void){
_start:
{
lean_object* v_nat_390_; lean_object* v_int_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_nat_390_ = l_Lean_Nat_mkType;
v_int_391_ = l_Lean_Int_mkType;
v___x_392_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__63, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__63_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__63);
v___x_393_ = l_Lean_mkAppB(v___x_392_, v_int_391_, v_nat_390_);
return v___x_393_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__98(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = l_Lean_Int_mkInstPowNat;
v___x_395_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__97, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__97_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__97);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_394_);
return v___x_396_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__99(void){
_start:
{
lean_object* v_int_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_int_397_ = l_Lean_Int_mkType;
v___x_398_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__68);
v___x_399_ = l_Lean_Expr_app___override(v___x_398_, v_int_397_);
return v___x_399_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__100(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = l_Lean_Int_mkInstPow;
v___x_401_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__99, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__99_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__99);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_400_);
return v___x_402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__103(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36);
v___x_407_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__102));
v___x_408_ = l_Lean_mkConst(v___x_407_, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__104(void){
_start:
{
lean_object* v_int_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_int_409_ = l_Lean_Int_mkType;
v___x_410_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__103, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__103_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__103);
v___x_411_ = l_Lean_Expr_app___override(v___x_410_, v_int_409_);
return v___x_411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__105(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = l_Lean_Int_mkInstNeg;
v___x_413_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__104, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__104_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__104);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_412_);
return v___x_414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__106(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_box(0);
v___x_416_ = lean_unsigned_to_nat(16u);
v___x_417_ = lean_mk_array(v___x_416_, v___x_415_);
return v___x_417_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__107(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__106, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__106_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__106);
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts(lean_object* v_leLvl_421_){
_start:
{
lean_object* v_nat_422_; lean_object* v_int_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_nat_422_ = l_Lean_Nat_mkType;
v_int_423_ = l_Lean_Int_mkType;
v___x_424_ = lean_box(0);
v___x_425_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__7, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__7_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__7);
v___x_426_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__12, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__12_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__12);
v___x_427_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__17, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__17_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__17);
v___x_428_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__22, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__22_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__22);
v___x_429_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__27, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__27_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__27);
v___x_430_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__32, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__32_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__32);
v___x_431_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__39, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__39_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__39);
v___x_432_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__44, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__44_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__44);
v___x_433_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__49, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__49_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__49);
v___x_434_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__54, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__54_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__54);
v___x_435_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__59, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__59_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__59);
v___x_436_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__65, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__65_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__65);
v___x_437_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__70, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__70_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__70);
v___x_438_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__72));
v___x_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_439_, 0, v_leLvl_421_);
lean_ctor_set(v___x_439_, 1, v___x_424_);
lean_inc_ref(v___x_439_);
v___x_440_ = l_Lean_mkConst(v___x_438_, v___x_439_);
lean_inc_ref(v___x_440_);
v___x_441_ = l_Lean_Expr_app___override(v___x_440_, v_nat_422_);
v___x_442_ = l_Lean_Nat_mkInstLT;
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__74));
v___x_445_ = l_Lean_mkConst(v___x_444_, v___x_439_);
lean_inc_ref(v___x_445_);
v___x_446_ = l_Lean_Expr_app___override(v___x_445_, v_nat_422_);
v___x_447_ = l_Lean_Nat_mkInstLE;
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__76, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__76_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__76);
v___x_450_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__78, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__78_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__78);
v___x_451_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__80, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__80_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__80);
v___x_452_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__82, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__82_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__82);
v___x_453_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__84, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__84_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__84);
v___x_454_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__86, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__86_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__86);
v___x_455_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__88, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__88_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__88);
v___x_456_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__90, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__90_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__90);
v___x_457_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__92, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__92_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__92);
v___x_458_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__94, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__94_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__94);
v___x_459_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__96, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__96_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__96);
v___x_460_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__98, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__98_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__98);
v___x_461_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__100, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__100_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__100);
v___x_462_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__105, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__105_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__105);
v___x_463_ = l_Lean_Expr_app___override(v___x_440_, v_int_423_);
v___x_464_ = l_Lean_Int_mkInstLT;
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_Expr_app___override(v___x_445_, v_int_423_);
v___x_467_ = l_Lean_Int_mkInstLE;
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_424_);
v___x_470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_465_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_462_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_461_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_460_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_459_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_458_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_457_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_456_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_455_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_454_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_453_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_452_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_451_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_450_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_449_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_448_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_443_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_437_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_436_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_435_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_434_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_433_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_432_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_431_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_430_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_429_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_428_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_427_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
v___x_498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_426_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_425_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__107, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__107_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__107);
v___x_501_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg(v___x_499_, v___x_500_);
lean_dec_ref_known(v___x_499_, 2);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0(lean_object* v_00_u03b2_502_, lean_object* v_m_503_, lean_object* v_a_504_, lean_object* v_b_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0___redArg(v_m_503_, v_a_504_, v_b_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1(lean_object* v_as_507_, lean_object* v_as_x27_508_, lean_object* v_b_509_, lean_object* v_a_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___redArg(v_as_x27_508_, v_b_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1___boxed(lean_object* v_as_512_, lean_object* v_as_x27_513_, lean_object* v_b_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__1(v_as_512_, v_as_x27_513_, v_b_514_, v_a_515_);
lean_dec(v_as_x27_513_);
lean_dec(v_as_512_);
return v_res_516_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_517_, lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
uint8_t v___x_520_; 
v___x_520_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___redArg(v_a_518_, v_x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_521_, lean_object* v_a_522_, lean_object* v_x_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__1(v_00_u03b2_521_, v_a_522_, v_x_523_);
lean_dec(v_x_523_);
lean_dec_ref(v_a_522_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_526_, lean_object* v_data_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2___redArg(v_data_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_529_, lean_object* v_a_530_, lean_object* v_b_531_, lean_object* v_x_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__3___redArg(v_a_530_, v_b_531_, v_x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_534_, lean_object* v_i_535_, lean_object* v_source_536_, lean_object* v_target_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3___redArg(v_i_535_, v_source_536_, v_target_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_540_, v_x_541_);
return v___x_542_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier___closed__0(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_box(0);
v___x_544_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts(v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier(void){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier___closed__0, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier___closed__0_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier___closed__0);
return v___x_545_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__0(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_box(0);
v___x_547_ = l_Lean_Level_succ___override(v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__1(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__0, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__0_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__0);
v___x_549_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts(v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier(void){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__1, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__1_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__1);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(lean_object* v_a_551_, lean_object* v_x_552_){
_start:
{
if (lean_obj_tag(v_x_552_) == 0)
{
lean_object* v___x_553_; 
v___x_553_ = lean_box(0);
return v___x_553_;
}
else
{
lean_object* v_key_554_; lean_object* v_value_555_; lean_object* v_tail_556_; uint8_t v___x_557_; 
v_key_554_ = lean_ctor_get(v_x_552_, 0);
v_value_555_ = lean_ctor_get(v_x_552_, 1);
v_tail_556_ = lean_ctor_get(v_x_552_, 2);
v___x_557_ = lean_expr_eqv(v_key_554_, v_a_551_);
if (v___x_557_ == 0)
{
v_x_552_ = v_tail_556_;
goto _start;
}
else
{
lean_object* v___x_559_; 
lean_inc(v_value_555_);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v_value_555_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_560_, lean_object* v_x_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(v_a_560_, v_x_561_);
lean_dec(v_x_561_);
lean_dec_ref(v_a_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(lean_object* v_m_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_buckets_565_; lean_object* v___x_566_; uint64_t v___x_567_; uint64_t v___x_568_; uint64_t v___x_569_; uint64_t v_fold_570_; uint64_t v___x_571_; uint64_t v___x_572_; uint64_t v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v___x_577_; size_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_buckets_565_ = lean_ctor_get(v_m_563_, 1);
v___x_566_ = lean_array_get_size(v_buckets_565_);
v___x_567_ = l_Lean_Expr_hash(v_a_564_);
v___x_568_ = 32ULL;
v___x_569_ = lean_uint64_shift_right(v___x_567_, v___x_568_);
v_fold_570_ = lean_uint64_xor(v___x_567_, v___x_569_);
v___x_571_ = 16ULL;
v___x_572_ = lean_uint64_shift_right(v_fold_570_, v___x_571_);
v___x_573_ = lean_uint64_xor(v_fold_570_, v___x_572_);
v___x_574_ = lean_uint64_to_usize(v___x_573_);
v___x_575_ = lean_usize_of_nat(v___x_566_);
v___x_576_ = ((size_t)1ULL);
v___x_577_ = lean_usize_sub(v___x_575_, v___x_576_);
v___x_578_ = lean_usize_land(v___x_574_, v___x_577_);
v___x_579_ = lean_array_uget_borrowed(v_buckets_565_, v___x_578_);
v___x_580_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(v_a_564_, v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg___boxed(lean_object* v_m_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v_m_581_, v_a_582_);
lean_dec_ref(v_a_582_);
lean_dec_ref(v_m_581_);
return v_res_583_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_box(0);
v___x_595_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__5));
v___x_596_ = l_Lean_mkConst(v___x_595_, v___x_594_);
return v___x_596_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__11(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_box(0);
v___x_605_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__10));
v___x_606_ = l_Lean_mkConst(v___x_605_, v___x_604_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__20(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_box(0);
v___x_620_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__19));
v___x_621_ = l_Lean_mkConst(v___x_620_, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__23(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_box(0);
v___x_626_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__22));
v___x_627_ = l_Lean_mkConst(v___x_626_, v___x_625_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__33(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_box(0);
v___x_647_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__32));
v___x_648_ = l_Lean_mkConst(v___x_647_, v___x_646_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__37(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_box(0);
v___x_657_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__36));
v___x_658_ = l_Lean_mkConst(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__40(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = lean_box(0);
v___x_663_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__39));
v___x_664_ = l_Lean_mkConst(v___x_663_, v___x_662_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__43(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_box(0);
v___x_670_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__42));
v___x_671_ = l_Lean_mkConst(v___x_670_, v___x_669_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f(uint8_t v_leCarrierIsSort_672_, lean_object* v_type_673_){
_start:
{
lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_703_; 
if (v_leCarrierIsSort_672_ == 0)
{
lean_object* v___x_779_; 
v___x_779_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier;
v___y_703_ = v___x_779_;
goto v___jp_702_;
}
else
{
lean_object* v___x_780_; 
v___x_780_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier;
v___y_703_ = v___x_780_;
goto v___jp_702_;
}
v___jp_674_:
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__1));
v___x_680_ = l_Lean_Expr_isConstOf(v___y_677_, v___x_679_);
lean_dec_ref(v___y_677_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
lean_dec_ref(v___y_678_);
lean_dec_ref(v___y_676_);
lean_dec_ref(v___y_675_);
v___x_681_ = lean_box(0);
return v___x_681_;
}
else
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__3));
v___x_683_ = l_Lean_Expr_isConstOf(v___y_675_, v___x_682_);
lean_dec_ref(v___y_675_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_dec_ref(v___y_678_);
lean_dec_ref(v___y_676_);
v___x_684_ = lean_box(0);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_685_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__6);
v___x_686_ = l_Lean_mkAppB(v___x_685_, v___y_676_, v___y_678_);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
}
v___jp_688_:
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__1));
v___x_694_ = l_Lean_Expr_isConstOf(v___y_691_, v___x_693_);
lean_dec_ref(v___y_691_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
lean_dec_ref(v___y_692_);
lean_dec_ref(v___y_690_);
lean_dec_ref(v___y_689_);
v___x_695_ = lean_box(0);
return v___x_695_;
}
else
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__8));
v___x_697_ = l_Lean_Expr_isConstOf(v___y_689_, v___x_696_);
lean_dec_ref(v___y_689_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
lean_dec_ref(v___y_692_);
lean_dec_ref(v___y_690_);
v___x_698_ = lean_box(0);
return v___x_698_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__11, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__11_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__11);
v___x_700_ = l_Lean_mkAppB(v___x_699_, v___y_690_, v___y_692_);
v___x_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
}
v___jp_702_:
{
lean_object* v___x_704_; 
v___x_704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v___y_703_, v_type_673_);
if (lean_obj_tag(v___x_704_) == 1)
{
return v___x_704_;
}
else
{
lean_object* v___x_705_; uint8_t v___x_706_; 
lean_dec(v___x_704_);
v___x_705_ = l_Lean_Expr_cleanupAnnotations(v_type_673_);
v___x_706_ = l_Lean_Expr_isApp(v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
lean_dec_ref(v___x_705_);
v___x_707_ = lean_box(0);
return v___x_707_;
}
else
{
lean_object* v_arg_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_arg_708_ = lean_ctor_get(v___x_705_, 1);
lean_inc_ref(v_arg_708_);
v___x_709_ = l_Lean_Expr_appFnCleanup___redArg(v___x_705_);
lean_dec_ref(v___x_705_);
v___x_710_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__13));
v___x_711_ = l_Lean_Expr_isConstOf(v___x_709_, v___x_710_);
if (v___x_711_ == 0)
{
uint8_t v___x_712_; 
v___x_712_ = l_Lean_Expr_isApp(v___x_709_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_dec_ref(v___x_709_);
lean_dec_ref(v_arg_708_);
v___x_713_ = lean_box(0);
return v___x_713_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_714_ = l_Lean_Expr_appFnCleanup___redArg(v___x_709_);
v___x_715_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__15));
v___x_716_ = l_Lean_Expr_isConstOf(v___x_714_, v___x_715_);
lean_dec_ref(v___x_714_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
lean_dec_ref(v___x_709_);
lean_dec_ref(v_arg_708_);
v___x_717_ = lean_box(0);
return v___x_717_;
}
else
{
lean_object* v_arg_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_arg_718_ = lean_ctor_get(v___x_709_, 1);
lean_inc_ref(v_arg_718_);
lean_dec_ref(v___x_709_);
v___x_719_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17));
v___x_720_ = l_Lean_Expr_isConstOf(v_arg_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__1));
v___x_722_ = l_Lean_Expr_isConstOf(v_arg_718_, v___x_721_);
lean_dec_ref(v_arg_718_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_dec_ref(v_arg_708_);
v___x_723_ = lean_box(0);
return v___x_723_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__20, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__20_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__20);
v___x_725_ = l_Lean_Expr_app___override(v___x_724_, v_arg_708_);
v___x_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec_ref(v_arg_718_);
v___x_727_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__23, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__23_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__23);
v___x_728_ = l_Lean_Expr_app___override(v___x_727_, v_arg_708_);
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
}
}
else
{
lean_object* v___x_730_; uint8_t v___x_731_; 
lean_dec_ref(v___x_709_);
v___x_730_ = l_Lean_Expr_cleanupAnnotations(v_arg_708_);
lean_dec_ref(v_arg_708_);
v___x_731_ = l_Lean_Expr_isApp(v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
lean_dec_ref(v___x_730_);
v___x_732_ = lean_box(0);
return v___x_732_;
}
else
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = l_Lean_Expr_appFnCleanup___redArg(v___x_730_);
v___x_734_ = l_Lean_Expr_isApp(v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; 
lean_dec_ref(v___x_733_);
lean_dec_ref(v___x_730_);
v___x_735_ = lean_box(0);
return v___x_735_;
}
else
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = l_Lean_Expr_appFnCleanup___redArg(v___x_733_);
v___x_737_ = l_Lean_Expr_isApp(v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
lean_dec_ref(v___x_736_);
lean_dec_ref(v___x_733_);
lean_dec_ref(v___x_730_);
v___x_738_ = lean_box(0);
return v___x_738_;
}
else
{
lean_object* v_arg_739_; lean_object* v_arg_740_; lean_object* v_arg_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_arg_739_ = lean_ctor_get(v___x_730_, 1);
lean_inc_ref(v_arg_739_);
lean_dec_ref(v___x_730_);
v_arg_740_ = lean_ctor_get(v___x_733_, 1);
lean_inc_ref(v_arg_740_);
lean_dec_ref(v___x_733_);
v_arg_741_ = lean_ctor_get(v___x_736_, 1);
lean_inc_ref(v_arg_741_);
v___x_742_ = l_Lean_Expr_appFnCleanup___redArg(v___x_736_);
lean_dec_ref(v___x_736_);
v___x_743_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__25));
v___x_744_ = l_Lean_Expr_isConstOf(v___x_742_, v___x_743_);
if (v___x_744_ == 0)
{
uint8_t v___x_745_; 
v___x_745_ = l_Lean_Expr_isApp(v___x_742_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_dec_ref(v___x_742_);
lean_dec_ref(v_arg_741_);
lean_dec_ref(v_arg_740_);
lean_dec_ref(v_arg_739_);
v___x_746_ = lean_box(0);
return v___x_746_;
}
else
{
lean_object* v_arg_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_arg_747_ = lean_ctor_get(v___x_742_, 1);
lean_inc_ref(v_arg_747_);
v___x_748_ = l_Lean_Expr_appFnCleanup___redArg(v___x_742_);
lean_dec_ref(v___x_742_);
v___x_749_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__27));
v___x_750_ = l_Lean_Expr_isConstOf(v___x_748_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__29));
v___x_752_ = l_Lean_Expr_isConstOf(v___x_748_, v___x_751_);
lean_dec_ref(v___x_748_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
lean_dec_ref(v_arg_747_);
lean_dec_ref(v_arg_741_);
lean_dec_ref(v_arg_740_);
lean_dec_ref(v_arg_739_);
v___x_753_ = lean_box(0);
return v___x_753_;
}
else
{
lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_754_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17));
v___x_755_ = l_Lean_Expr_isConstOf(v_arg_747_, v___x_754_);
if (v___x_755_ == 0)
{
v___y_689_ = v_arg_741_;
v___y_690_ = v_arg_740_;
v___y_691_ = v_arg_747_;
v___y_692_ = v_arg_739_;
goto v___jp_688_;
}
else
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31));
v___x_757_ = l_Lean_Expr_isConstOf(v_arg_741_, v___x_756_);
if (v___x_757_ == 0)
{
v___y_689_ = v_arg_741_;
v___y_690_ = v_arg_740_;
v___y_691_ = v_arg_747_;
v___y_692_ = v_arg_739_;
goto v___jp_688_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
lean_dec_ref(v_arg_747_);
lean_dec_ref(v_arg_741_);
v___x_758_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__33, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__33_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__33);
v___x_759_ = l_Lean_mkAppB(v___x_758_, v_arg_740_, v_arg_739_);
v___x_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
}
}
}
else
{
lean_object* v___x_761_; uint8_t v___x_762_; 
lean_dec_ref(v___x_748_);
v___x_761_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17));
v___x_762_ = l_Lean_Expr_isConstOf(v_arg_747_, v___x_761_);
if (v___x_762_ == 0)
{
v___y_675_ = v_arg_741_;
v___y_676_ = v_arg_740_;
v___y_677_ = v_arg_747_;
v___y_678_ = v_arg_739_;
goto v___jp_674_;
}
else
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35));
v___x_764_ = l_Lean_Expr_isConstOf(v_arg_741_, v___x_763_);
if (v___x_764_ == 0)
{
v___y_675_ = v_arg_741_;
v___y_676_ = v_arg_740_;
v___y_677_ = v_arg_747_;
v___y_678_ = v_arg_739_;
goto v___jp_674_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec_ref(v_arg_747_);
lean_dec_ref(v_arg_741_);
v___x_765_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__37, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__37_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__37);
v___x_766_ = l_Lean_mkAppB(v___x_765_, v_arg_740_, v_arg_739_);
v___x_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
}
}
}
else
{
lean_object* v___x_768_; uint8_t v___x_769_; 
lean_dec_ref(v___x_742_);
v___x_768_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17));
v___x_769_ = l_Lean_Expr_isConstOf(v_arg_741_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__1));
v___x_771_ = l_Lean_Expr_isConstOf(v_arg_741_, v___x_770_);
lean_dec_ref(v_arg_741_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_dec_ref(v_arg_740_);
lean_dec_ref(v_arg_739_);
v___x_772_ = lean_box(0);
return v___x_772_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__40, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__40_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__40);
v___x_774_ = l_Lean_mkAppB(v___x_773_, v_arg_740_, v_arg_739_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec_ref(v_arg_741_);
v___x_776_ = lean_obj_once(&l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__43, &l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__43_once, _init_l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__43);
v___x_777_ = l_Lean_mkAppB(v___x_776_, v_arg_740_, v_arg_739_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBuiltinInstance_x3f___boxed(lean_object* v_leCarrierIsSort_781_, lean_object* v_type_782_){
_start:
{
uint8_t v_leCarrierIsSort_boxed_783_; lean_object* v_res_784_; 
v_leCarrierIsSort_boxed_783_ = lean_unbox(v_leCarrierIsSort_781_);
v_res_784_ = l_Lean_Meta_Sym_getBuiltinInstance_x3f(v_leCarrierIsSort_boxed_783_, v_type_782_);
lean_dec_ref(v_type_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0(lean_object* v_00_u03b2_785_, lean_object* v_m_786_, lean_object* v_a_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v_m_786_, v_a_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___boxed(lean_object* v_00_u03b2_789_, lean_object* v_m_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0(v_00_u03b2_789_, v_m_790_, v_a_791_);
lean_dec_ref(v_a_791_);
lean_dec_ref(v_m_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0(lean_object* v_00_u03b2_793_, lean_object* v_a_794_, lean_object* v_x_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(v_a_794_, v_x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_797_, lean_object* v_a_798_, lean_object* v_x_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0(v_00_u03b2_797_, v_a_798_, v_x_799_);
lean_dec(v_x_799_);
lean_dec_ref(v_a_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(lean_object* v_leLvl_801_, lean_object* v___x_802_, lean_object* v_n_803_, lean_object* v_args_804_){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_805_, 0, v_leLvl_801_);
lean_ctor_set(v___x_805_, 1, v___x_802_);
v___x_806_ = l_Lean_mkConst(v_n_803_, v___x_805_);
v___x_807_ = l_Lean_mkAppN(v___x_806_, v_args_804_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0___boxed(lean_object* v_leLvl_808_, lean_object* v___x_809_, lean_object* v_n_810_, lean_object* v_args_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(v_leLvl_808_, v___x_809_, v_n_810_, v_args_811_);
lean_dec_ref(v_args_811_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(lean_object* v_z_813_, lean_object* v_n_814_, lean_object* v_args_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = l_Lean_mkConst(v_n_814_, v_z_813_);
v___x_817_ = l_Lean_mkAppN(v___x_816_, v_args_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1___boxed(lean_object* v_z_818_, lean_object* v_n_819_, lean_object* v_args_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_818_, v_n_819_, v_args_820_);
lean_dec_ref(v_args_820_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0_spec__0___redArg(lean_object* v_as_x27_822_, lean_object* v_b_823_){
_start:
{
if (lean_obj_tag(v_as_x27_822_) == 0)
{
return v_b_823_;
}
else
{
lean_object* v_head_824_; lean_object* v_tail_825_; lean_object* v_fst_826_; lean_object* v_snd_827_; lean_object* v_r_828_; 
v_head_824_ = lean_ctor_get(v_as_x27_822_, 0);
v_tail_825_ = lean_ctor_get(v_as_x27_822_, 1);
v_fst_826_ = lean_ctor_get(v_head_824_, 0);
v_snd_827_ = lean_ctor_get(v_head_824_, 1);
lean_inc(v_snd_827_);
lean_inc(v_fst_826_);
v_r_828_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts_spec__0_spec__0___redArg(v_b_823_, v_fst_826_, v_snd_827_);
v_as_x27_822_ = v_tail_825_;
v_b_823_ = v_r_828_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0_spec__0___redArg___boxed(lean_object* v_as_x27_830_, lean_object* v_b_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0_spec__0___redArg(v_as_x27_830_, v_b_831_);
lean_dec(v_as_x27_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0(lean_object* v_m_833_, lean_object* v_l_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0_spec__0___redArg(v_l_834_, v_m_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0___boxed(lean_object* v_m_836_, lean_object* v_l_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0(v_m_836_, v_l_837_);
lean_dec(v_l_837_);
return v_res_838_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__0(void){
_start:
{
lean_object* v___x_839_; lean_object* v_prop_840_; 
v___x_839_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__35);
v_prop_840_ = l_Lean_mkSort(v___x_839_);
return v_prop_840_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__5(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_crI_850_; 
v___x_848_ = lean_box(0);
v___x_849_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__4));
v_crI_850_ = l_Lean_mkConst(v___x_849_, v___x_848_);
return v_crI_850_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9(void){
_start:
{
lean_object* v_int_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_int_858_ = l_Lean_Int_mkType;
v___x_859_ = lean_unsigned_to_nat(2u);
v___x_860_ = lean_mk_empty_array_with_capacity(v___x_859_);
v___x_861_ = lean_array_push(v___x_860_, v_int_858_);
return v___x_861_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__10(void){
_start:
{
lean_object* v_crI_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_crI_862_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__5, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__5_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__5);
v___x_863_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9);
v___x_864_ = lean_array_push(v___x_863_, v_crI_862_);
return v___x_864_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__11(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v_z_867_; lean_object* v_ringI_868_; 
v___x_865_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__10, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__10_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__10);
v___x_866_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__8));
v_z_867_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v_ringI_868_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_867_, v___x_866_, v___x_865_);
return v_ringI_868_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__15(void){
_start:
{
lean_object* v_ringI_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_ringI_876_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__11, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__11_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__11);
v___x_877_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9);
v___x_878_ = lean_array_push(v___x_877_, v_ringI_876_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__16(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_z_881_; lean_object* v_srI_882_; 
v___x_879_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__15, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__15_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__15);
v___x_880_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__14));
v_z_881_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v_srI_882_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_881_, v___x_880_, v___x_879_);
return v_srI_882_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__19(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v_z_891_; lean_object* v_csI_892_; 
v___x_889_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__10, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__10_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__10);
v___x_890_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__18));
v_z_891_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v_csI_892_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_891_, v___x_890_, v___x_889_);
return v_csI_892_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__25(void){
_start:
{
lean_object* v_csI_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_csI_906_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__19, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__19_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__19);
v___x_907_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9);
v___x_908_ = lean_array_push(v___x_907_, v_csI_906_);
return v___x_908_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__26(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v_z_911_; lean_object* v___x_912_; 
v___x_909_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__25, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__25_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__25);
v___x_910_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__24));
v_z_911_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_912_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_911_, v___x_910_, v___x_909_);
return v___x_912_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__27(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__26, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__26_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__26);
v___x_914_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9);
v___x_915_ = lean_array_push(v___x_914_, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__28(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v_z_918_; lean_object* v_nmI_919_; 
v___x_916_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__27, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__27_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__27);
v___x_917_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__22));
v_z_918_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v_nmI_919_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_918_, v___x_917_, v___x_916_);
return v_nmI_919_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__31(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_lopI_926_; 
v___x_924_ = lean_box(0);
v___x_925_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__30));
v_lopI_926_ = l_Lean_mkConst(v___x_925_, v___x_924_);
return v_lopI_926_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__36(void){
_start:
{
lean_object* v_lopI_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_lopI_934_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__31, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__31_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__31);
v___x_935_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9);
v___x_936_ = lean_array_push(v___x_935_, v_lopI_934_);
return v___x_936_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__37(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v_z_939_; lean_object* v_lppI_940_; 
v___x_937_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__36);
v___x_938_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__35));
v_z_939_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v_lppI_940_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_939_, v___x_938_, v___x_937_);
return v_lppI_940_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__44(void){
_start:
{
lean_object* v_lppI_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_lppI_953_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__37, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__37_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__37);
v___x_954_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9);
v___x_955_ = lean_array_push(v___x_954_, v_lppI_953_);
return v___x_955_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__45(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_z_958_; lean_object* v___x_959_; 
v___x_956_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__44, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__44_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__44);
v___x_957_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__43));
v_z_958_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_959_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_958_, v___x_957_, v___x_956_);
return v___x_959_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__46(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__45, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__45_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__45);
v___x_961_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9);
v___x_962_ = lean_array_push(v___x_961_, v___x_960_);
return v___x_962_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__47(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v_z_965_; lean_object* v_preI_966_; 
v___x_963_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__46, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__46_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__46);
v___x_964_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__40));
v_z_965_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v_preI_966_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_965_, v___x_964_, v___x_963_);
return v_preI_966_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__48(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v_leI_969_; 
v___x_967_ = lean_box(0);
v___x_968_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__31));
v_leI_969_ = l_Lean_mkConst(v___x_968_, v___x_967_);
return v_leI_969_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__49(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_ltI_972_; 
v___x_970_ = lean_box(0);
v___x_971_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__35));
v_ltI_972_ = l_Lean_mkConst(v___x_971_, v___x_970_);
return v_ltI_972_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__52(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_csN_980_; 
v___x_978_ = lean_box(0);
v___x_979_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__51));
v_csN_980_ = l_Lean_mkConst(v___x_979_, v___x_978_);
return v_csN_980_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53(void){
_start:
{
lean_object* v_nat_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_nat_981_ = l_Lean_Nat_mkType;
v___x_982_ = lean_unsigned_to_nat(2u);
v___x_983_ = lean_mk_empty_array_with_capacity(v___x_982_);
v___x_984_ = lean_array_push(v___x_983_, v_nat_981_);
return v___x_984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__54(void){
_start:
{
lean_object* v_csN_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_csN_985_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__52, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__52_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__52);
v___x_986_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53);
v___x_987_ = lean_array_push(v___x_986_, v_csN_985_);
return v___x_987_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__55(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_z_990_; lean_object* v_srN_991_; 
v___x_988_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__54, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__54_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__54);
v___x_989_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__24));
v_z_990_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v_srN_991_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_990_, v___x_989_, v___x_988_);
return v_srN_991_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__56(void){
_start:
{
lean_object* v_srN_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_srN_992_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__55, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__55_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__55);
v___x_993_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53);
v___x_994_ = lean_array_push(v___x_993_, v_srN_992_);
return v___x_994_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__57(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_z_997_; lean_object* v_nmN_998_; 
v___x_995_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__56, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__56_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__56);
v___x_996_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__22));
v_z_997_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v_nmN_998_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_997_, v___x_996_, v___x_995_);
return v_nmN_998_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_leN_1001_; 
v___x_999_ = lean_box(0);
v___x_1000_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__8));
v_leN_1001_ = l_Lean_mkConst(v___x_1000_, v___x_999_);
return v_leN_1001_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__59(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v_ltN_1004_; 
v___x_1002_ = lean_box(0);
v___x_1003_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__3));
v_ltN_1004_ = l_Lean_mkConst(v___x_1003_, v___x_1002_);
return v_ltN_1004_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__62(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v_preN_1012_; 
v___x_1010_ = lean_box(0);
v___x_1011_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__61));
v_preN_1012_ = l_Lean_mkConst(v___x_1011_, v___x_1010_);
return v_preN_1012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__65(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_linN_1019_; 
v___x_1017_ = lean_box(0);
v___x_1018_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__64));
v_linN_1019_ = l_Lean_mkConst(v___x_1018_, v___x_1017_);
return v_linN_1019_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68(void){
_start:
{
lean_object* v_nat_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_nat_1023_ = l_Lean_Nat_mkType;
v___x_1024_ = lean_unsigned_to_nat(1u);
v___x_1025_ = lean_mk_empty_array_with_capacity(v___x_1024_);
v___x_1026_ = lean_array_push(v___x_1025_, v_nat_1023_);
return v___x_1026_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__69(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_z_1029_; lean_object* v___x_1030_; 
v___x_1027_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68);
v___x_1028_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__67));
v_z_1029_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1030_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1029_, v___x_1028_, v___x_1027_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__72(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = lean_box(0);
v___x_1036_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__71));
v___x_1037_ = l_Lean_mkConst(v___x_1036_, v___x_1035_);
return v___x_1037_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__73(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__72, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__72_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__72);
v___x_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__74(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__73, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__73_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__73);
v___x_1041_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__69, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__69_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__69);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___x_1040_);
return v___x_1042_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76(void){
_start:
{
lean_object* v_prop_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_prop_1047_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__0, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__0_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__0);
v___x_1048_ = lean_unsigned_to_nat(1u);
v___x_1049_ = lean_mk_empty_array_with_capacity(v___x_1048_);
v___x_1050_ = lean_array_push(v___x_1049_, v_prop_1047_);
return v___x_1050_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__77(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v_z_1053_; lean_object* v___x_1054_; 
v___x_1051_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76);
v___x_1052_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__75));
v_z_1053_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1054_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1053_, v___x_1052_, v___x_1051_);
return v___x_1054_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__78(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1055_ = lean_box(0);
v___x_1056_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__77, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__77_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__77);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___x_1055_);
return v___x_1057_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__80(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_z_1064_; lean_object* v___x_1065_; 
v___x_1062_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76);
v___x_1063_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__79));
v_z_1064_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1065_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1064_, v___x_1063_, v___x_1062_);
return v___x_1065_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__81(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__80, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__80_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__80);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v___x_1066_);
return v___x_1068_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__83(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v_z_1075_; lean_object* v___x_1076_; 
v___x_1073_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76);
v___x_1074_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__82));
v_z_1075_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1076_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1075_, v___x_1074_, v___x_1073_);
return v___x_1076_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__84(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__83, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__83_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__83);
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___x_1077_);
return v___x_1079_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__86(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v_z_1086_; lean_object* v___x_1087_; 
v___x_1084_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__76);
v___x_1085_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__85));
v_z_1086_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1087_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1086_, v___x_1085_, v___x_1084_);
return v___x_1087_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__87(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__86, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__86_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__86);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v___x_1088_);
return v___x_1090_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__88(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_box(0);
v___x_1092_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__87, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__87_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__87);
v___x_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v___x_1091_);
return v___x_1093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__89(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__88, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__88_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__88);
v___x_1095_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__84, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__84_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__84);
v___x_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v___x_1094_);
return v___x_1096_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__90(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__89, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__89_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__89);
v___x_1098_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__81, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__81_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__81);
v___x_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v___x_1097_);
return v___x_1099_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__91(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__90, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__90_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__90);
v___x_1101_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__78, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__78_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__78);
v___x_1102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v___x_1100_);
return v___x_1102_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__92(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_x_1105_; 
v___x_1103_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__91, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__91_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__91);
v___x_1104_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__74, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__74_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__74);
v_x_1105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1105_, 0, v___x_1104_);
lean_ctor_set(v_x_1105_, 1, v___x_1103_);
return v_x_1105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__95(void){
_start:
{
lean_object* v_leN_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_leN_1110_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58);
v___x_1111_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53);
v___x_1112_ = lean_array_push(v___x_1111_, v_leN_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__96(void){
_start:
{
lean_object* v_linN_1113_; lean_object* v___x_1114_; 
v_linN_1113_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__65, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__65_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__65);
v___x_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_linN_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__99(void){
_start:
{
lean_object* v_nat_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_nat_1119_ = l_Lean_Nat_mkType;
v___x_1120_ = lean_unsigned_to_nat(3u);
v___x_1121_ = lean_mk_empty_array_with_capacity(v___x_1120_);
v___x_1122_ = lean_array_push(v___x_1121_, v_nat_1119_);
return v___x_1122_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__100(void){
_start:
{
lean_object* v_ltN_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_ltN_1123_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__59, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__59_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__59);
v___x_1124_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__99, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__99_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__99);
v___x_1125_ = lean_array_push(v___x_1124_, v_ltN_1123_);
return v___x_1125_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__101(void){
_start:
{
lean_object* v_leN_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_leN_1126_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58);
v___x_1127_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__100, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__100_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__100);
v___x_1128_ = lean_array_push(v___x_1127_, v_leN_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__104(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = lean_box(0);
v___x_1135_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__103));
v___x_1136_ = l_Lean_mkConst(v___x_1135_, v___x_1134_);
return v___x_1136_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__105(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__104, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__104_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__104);
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__108(void){
_start:
{
lean_object* v_preN_1144_; lean_object* v_ltN_1145_; lean_object* v_leN_1146_; lean_object* v_srN_1147_; lean_object* v_nat_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v_preN_1144_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__62, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__62_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__62);
v_ltN_1145_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__59, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__59_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__59);
v_leN_1146_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58);
v_srN_1147_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__55, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__55_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__55);
v_nat_1148_ = l_Lean_Nat_mkType;
v___x_1149_ = lean_unsigned_to_nat(5u);
v___x_1150_ = lean_mk_empty_array_with_capacity(v___x_1149_);
v___x_1151_ = lean_array_push(v___x_1150_, v_nat_1148_);
v___x_1152_ = lean_array_push(v___x_1151_, v_srN_1147_);
v___x_1153_ = lean_array_push(v___x_1152_, v_leN_1146_);
v___x_1154_ = lean_array_push(v___x_1153_, v_ltN_1145_);
v___x_1155_ = lean_array_push(v___x_1154_, v_preN_1144_);
return v___x_1155_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__109(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v_z_1158_; lean_object* v___x_1159_; 
v___x_1156_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__108, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__108_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__108);
v___x_1157_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__107));
v_z_1158_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1159_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1158_, v___x_1157_, v___x_1156_);
return v___x_1159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__112(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_box(0);
v___x_1166_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__111));
v___x_1167_ = l_Lean_mkConst(v___x_1166_, v___x_1165_);
return v___x_1167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__113(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__112, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__112_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__112);
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__114(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__113, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__113_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__113);
v___x_1171_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__109, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__109_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__109);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v___x_1170_);
return v___x_1172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__117(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_z_1178_; lean_object* v___x_1179_; 
v___x_1176_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68);
v___x_1177_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__116));
v_z_1178_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1179_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1178_, v___x_1177_, v___x_1176_);
return v___x_1179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__120(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = lean_box(0);
v___x_1184_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__119));
v___x_1185_ = l_Lean_mkConst(v___x_1184_, v___x_1183_);
return v___x_1185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__121(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__120, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__120_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__120);
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__122(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__121, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__121_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__121);
v___x_1189_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__117, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__117_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__117);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v___x_1188_);
return v___x_1190_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__125(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v_z_1196_; lean_object* v___x_1197_; 
v___x_1194_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68);
v___x_1195_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__124));
v_z_1196_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1197_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1196_, v___x_1195_, v___x_1194_);
return v___x_1197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__128(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = lean_box(0);
v___x_1203_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__127));
v___x_1204_ = l_Lean_mkConst(v___x_1203_, v___x_1202_);
return v___x_1204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__129(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__128, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__128_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__128);
v___x_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__130(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__129, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__129_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__129);
v___x_1208_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__125, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__125_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__125);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1207_);
return v___x_1209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__131(void){
_start:
{
lean_object* v_x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_x_1210_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__92, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__92_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__92);
v___x_1211_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__130, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__130_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__130);
v___x_1212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v_x_1210_);
return v___x_1212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__132(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__131, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__131_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__131);
v___x_1214_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__122, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__122_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__122);
v___x_1215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___x_1213_);
return v___x_1215_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__133(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__132, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__132_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__132);
v___x_1217_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__114, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__114_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__114);
v___x_1218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v___x_1216_);
return v___x_1218_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__136(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_z_1226_; lean_object* v___x_1227_; 
v___x_1224_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68);
v___x_1225_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__135));
v_z_1226_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1227_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1226_, v___x_1225_, v___x_1224_);
return v___x_1227_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__137(void){
_start:
{
lean_object* v_nmN_1228_; lean_object* v___x_1229_; 
v_nmN_1228_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__57, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__57_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__57);
v___x_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1229_, 0, v_nmN_1228_);
return v___x_1229_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__138(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1230_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__137, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__137_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__137);
v___x_1231_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__136, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__136_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__136);
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v___x_1230_);
return v___x_1232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__141(void){
_start:
{
lean_object* v_nmN_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_nmN_1238_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__57, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__57_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__57);
v___x_1239_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53);
v___x_1240_ = lean_array_push(v___x_1239_, v_nmN_1238_);
return v___x_1240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__142(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v_z_1243_; lean_object* v___x_1244_; 
v___x_1241_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__141, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__141_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__141);
v___x_1242_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__140));
v_z_1243_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1244_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1243_, v___x_1242_, v___x_1241_);
return v___x_1244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__145(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = lean_box(0);
v___x_1251_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__144));
v___x_1252_ = l_Lean_mkConst(v___x_1251_, v___x_1250_);
return v___x_1252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__146(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__145, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__145_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__145);
v___x_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__147(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__146, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__146_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__146);
v___x_1256_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__142, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__142_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__142);
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v___x_1255_);
return v___x_1257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__150(void){
_start:
{
lean_object* v_preN_1262_; lean_object* v___x_1263_; 
v_preN_1262_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__62, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__62_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__62);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_preN_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__155(void){
_start:
{
lean_object* v_leN_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_leN_1273_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__58);
v___x_1274_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__99, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__99_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__99);
v___x_1275_ = lean_array_push(v___x_1274_, v_leN_1273_);
return v___x_1275_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__156(void){
_start:
{
lean_object* v_linN_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_linN_1276_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__65, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__65_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__65);
v___x_1277_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__155, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__155_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__155);
v___x_1278_ = lean_array_push(v___x_1277_, v_linN_1276_);
return v___x_1278_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__163(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_z_1295_; lean_object* v___x_1296_; 
v___x_1293_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68);
v___x_1294_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__162));
v_z_1295_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1296_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1295_, v___x_1294_, v___x_1293_);
return v___x_1296_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__164(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = lean_box(0);
v___x_1298_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__163, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__163_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__163);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v___x_1297_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__165(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_z_1302_; lean_object* v___x_1303_; 
v___x_1300_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68);
v___x_1301_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__82));
v_z_1302_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1303_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1302_, v___x_1301_, v___x_1300_);
return v___x_1303_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__166(void){
_start:
{
lean_object* v_csN_1304_; lean_object* v___x_1305_; 
v_csN_1304_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__52, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__52_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__52);
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_csN_1304_);
return v___x_1305_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__167(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__166, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__166_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__166);
v___x_1307_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__165, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__165_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__165);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v___x_1306_);
return v___x_1308_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__168(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v_z_1311_; lean_object* v___x_1312_; 
v___x_1309_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68);
v___x_1310_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__85));
v_z_1311_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1312_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1311_, v___x_1310_, v___x_1309_);
return v___x_1312_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__169(void){
_start:
{
lean_object* v_srN_1313_; lean_object* v___x_1314_; 
v_srN_1313_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__55, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__55_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__55);
v___x_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_srN_1313_);
return v___x_1314_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__170(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__169, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__169_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__169);
v___x_1316_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__168, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__168_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__168);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v___x_1315_);
return v___x_1317_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__175(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = lean_box(0);
v___x_1327_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__174));
v___x_1328_ = l_Lean_mkConst(v___x_1327_, v___x_1326_);
return v___x_1328_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__176(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__175, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__175_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__175);
v___x_1330_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__53);
v___x_1331_ = lean_array_push(v___x_1330_, v___x_1329_);
return v___x_1331_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__177(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_z_1334_; lean_object* v___x_1335_; 
v___x_1332_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__176, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__176_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__176);
v___x_1333_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__172));
v_z_1334_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1335_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1334_, v___x_1333_, v___x_1332_);
return v___x_1335_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__180(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = lean_box(0);
v___x_1342_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__179));
v___x_1343_ = l_Lean_mkConst(v___x_1342_, v___x_1341_);
return v___x_1343_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__181(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__180, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__180_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__180);
v___x_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
return v___x_1345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__182(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__181, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__181_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__181);
v___x_1347_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__177, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__177_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__177);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v___x_1346_);
return v___x_1348_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183(void){
_start:
{
lean_object* v_int_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_int_1349_ = l_Lean_Int_mkType;
v___x_1350_ = lean_unsigned_to_nat(1u);
v___x_1351_ = lean_mk_empty_array_with_capacity(v___x_1350_);
v___x_1352_ = lean_array_push(v___x_1351_, v_int_1349_);
return v___x_1352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__184(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_z_1355_; lean_object* v___x_1356_; 
v___x_1353_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183);
v___x_1354_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__116));
v_z_1355_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1356_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1355_, v___x_1354_, v___x_1353_);
return v___x_1356_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__187(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_box(0);
v___x_1361_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__186));
v___x_1362_ = l_Lean_mkConst(v___x_1361_, v___x_1360_);
return v___x_1362_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__188(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__187, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__187_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__187);
v___x_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__189(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1365_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__188, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__188_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__188);
v___x_1366_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__184, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__184_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__184);
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
lean_ctor_set(v___x_1367_, 1, v___x_1365_);
return v___x_1367_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__190(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v_z_1370_; lean_object* v___x_1371_; 
v___x_1368_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183);
v___x_1369_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__124));
v_z_1370_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1371_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1370_, v___x_1369_, v___x_1368_);
return v___x_1371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__192(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__191));
v___x_1377_ = l_Lean_mkConst(v___x_1376_, v___x_1375_);
return v___x_1377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__193(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__192, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__192_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__192);
v___x_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
return v___x_1379_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__194(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__193, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__193_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__193);
v___x_1381_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__190, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__190_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__190);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set(v___x_1382_, 1, v___x_1380_);
return v___x_1382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__195(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v_z_1385_; lean_object* v___x_1386_; 
v___x_1383_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183);
v___x_1384_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__67));
v_z_1385_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1386_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1385_, v___x_1384_, v___x_1383_);
return v___x_1386_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__197(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_box(0);
v___x_1391_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__196));
v___x_1392_ = l_Lean_mkConst(v___x_1391_, v___x_1390_);
return v___x_1392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__198(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__197, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__197_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__197);
v___x_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__199(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__198, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__198_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__198);
v___x_1396_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__195, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__195_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__195);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v___x_1395_);
return v___x_1397_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__200(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v_z_1400_; lean_object* v___x_1401_; 
v___x_1398_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68);
v___x_1399_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__75));
v_z_1400_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1401_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1400_, v___x_1399_, v___x_1398_);
return v___x_1401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__201(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__200, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__200_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__200);
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
lean_ctor_set(v___x_1404_, 1, v___x_1402_);
return v___x_1404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__202(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v_z_1407_; lean_object* v___x_1408_; 
v___x_1405_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__68);
v___x_1406_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__79));
v_z_1407_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1408_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1407_, v___x_1406_, v___x_1405_);
return v___x_1408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__203(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = lean_box(0);
v___x_1410_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__202, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__202_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__202);
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v___x_1409_);
return v___x_1411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__204(void){
_start:
{
lean_object* v_leI_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_leI_1412_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__48, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__48_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__48);
v___x_1413_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9);
v___x_1414_ = lean_array_push(v___x_1413_, v_leI_1412_);
return v___x_1414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__206(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v_z_1421_; lean_object* v___x_1422_; 
v___x_1419_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__44, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__44_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__44);
v___x_1420_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__205));
v_z_1421_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1422_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1421_, v___x_1420_, v___x_1419_);
return v___x_1422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__207(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__206, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__206_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__206);
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
return v___x_1424_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__210(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__209));
v___x_1432_ = l_Lean_mkConst(v___x_1431_, v___x_1430_);
return v___x_1432_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__211(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__210, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__210_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__210);
v___x_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
return v___x_1434_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__212(void){
_start:
{
lean_object* v_leI_1435_; lean_object* v_ltI_1436_; lean_object* v_int_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_leI_1435_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__48, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__48_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__48);
v_ltI_1436_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__49, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__49_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__49);
v_int_1437_ = l_Lean_Int_mkType;
v___x_1438_ = lean_unsigned_to_nat(3u);
v___x_1439_ = lean_mk_empty_array_with_capacity(v___x_1438_);
v___x_1440_ = lean_array_push(v___x_1439_, v_int_1437_);
v___x_1441_ = lean_array_push(v___x_1440_, v_ltI_1436_);
v___x_1442_ = lean_array_push(v___x_1441_, v_leI_1435_);
return v___x_1442_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__215(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1448_ = lean_box(0);
v___x_1449_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__214));
v___x_1450_ = l_Lean_mkConst(v___x_1449_, v___x_1448_);
return v___x_1450_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__216(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__215, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__215_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__215);
v___x_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__217(void){
_start:
{
lean_object* v_preI_1453_; lean_object* v_ltI_1454_; lean_object* v_leI_1455_; lean_object* v_srI_1456_; lean_object* v_int_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v_preI_1453_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__47, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__47_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__47);
v_ltI_1454_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__49, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__49_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__49);
v_leI_1455_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__48, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__48_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__48);
v_srI_1456_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__16, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__16_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__16);
v_int_1457_ = l_Lean_Int_mkType;
v___x_1458_ = lean_unsigned_to_nat(5u);
v___x_1459_ = lean_mk_empty_array_with_capacity(v___x_1458_);
v___x_1460_ = lean_array_push(v___x_1459_, v_int_1457_);
v___x_1461_ = lean_array_push(v___x_1460_, v_srI_1456_);
v___x_1462_ = lean_array_push(v___x_1461_, v_leI_1455_);
v___x_1463_ = lean_array_push(v___x_1462_, v_ltI_1454_);
v___x_1464_ = lean_array_push(v___x_1463_, v_preI_1453_);
return v___x_1464_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__218(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v_z_1467_; lean_object* v___x_1468_; 
v___x_1465_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__217, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__217_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__217);
v___x_1466_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__107));
v_z_1467_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1468_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1467_, v___x_1466_, v___x_1465_);
return v___x_1468_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__221(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = lean_box(0);
v___x_1475_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__220));
v___x_1476_ = l_Lean_mkConst(v___x_1475_, v___x_1474_);
return v___x_1476_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__222(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__221, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__221_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__221);
v___x_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__223(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__222, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__222_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__222);
v___x_1480_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__218, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__218_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__218);
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v___x_1479_);
return v___x_1481_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__224(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_z_1484_; lean_object* v___x_1485_; 
v___x_1482_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183);
v___x_1483_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__162));
v_z_1484_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1485_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1484_, v___x_1483_, v___x_1482_);
return v___x_1485_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__225(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = lean_box(0);
v___x_1487_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__224, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__224_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__224);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v___x_1486_);
return v___x_1488_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__226(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_z_1491_; lean_object* v___x_1492_; 
v___x_1489_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183);
v___x_1490_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__135));
v_z_1491_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1492_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1491_, v___x_1490_, v___x_1489_);
return v___x_1492_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__227(void){
_start:
{
lean_object* v_nmI_1493_; lean_object* v___x_1494_; 
v_nmI_1493_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__28, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__28_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__28);
v___x_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1494_, 0, v_nmI_1493_);
return v___x_1494_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__228(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__227, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__227_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__227);
v___x_1496_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__226, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__226_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__226);
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_ctor_set(v___x_1497_, 1, v___x_1495_);
return v___x_1497_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__229(void){
_start:
{
lean_object* v_nmI_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_nmI_1498_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__28, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__28_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__28);
v___x_1499_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9);
v___x_1500_ = lean_array_push(v___x_1499_, v_nmI_1498_);
return v___x_1500_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__230(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v_z_1503_; lean_object* v___x_1504_; 
v___x_1501_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__229, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__229_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__229);
v___x_1502_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__140));
v_z_1503_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1504_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1503_, v___x_1502_, v___x_1501_);
return v___x_1504_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__233(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = lean_box(0);
v___x_1511_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__232));
v___x_1512_ = l_Lean_mkConst(v___x_1511_, v___x_1510_);
return v___x_1512_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__234(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__233, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__233_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__233);
v___x_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__235(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__234, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__234_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__234);
v___x_1516_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__230, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__230_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__230);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v___x_1515_);
return v___x_1517_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__236(void){
_start:
{
lean_object* v_preI_1518_; lean_object* v___x_1519_; 
v_preI_1518_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__47, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__47_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__47);
v___x_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1519_, 0, v_preI_1518_);
return v___x_1519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__241(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_z_1532_; lean_object* v___x_1533_; 
v___x_1530_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__36);
v___x_1531_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__240));
v_z_1532_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1533_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1532_, v___x_1531_, v___x_1530_);
return v___x_1533_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__242(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1534_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__241, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__241_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__241);
v___x_1535_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__9);
v___x_1536_ = lean_array_push(v___x_1535_, v___x_1534_);
return v___x_1536_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__243(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v_z_1539_; lean_object* v___x_1540_; 
v___x_1537_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__242, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__242_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__242);
v___x_1538_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__238));
v_z_1539_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1540_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1539_, v___x_1538_, v___x_1537_);
return v___x_1540_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__244(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__243, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__243_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__243);
v___x_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__245(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v_z_1545_; lean_object* v___x_1546_; 
v___x_1543_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183);
v___x_1544_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__75));
v_z_1545_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1546_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1545_, v___x_1544_, v___x_1543_);
return v___x_1546_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__246(void){
_start:
{
lean_object* v_crI_1547_; lean_object* v___x_1548_; 
v_crI_1547_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__5, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__5_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__5);
v___x_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_crI_1547_);
return v___x_1548_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__247(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__246, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__246_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__246);
v___x_1550_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__245, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__245_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__245);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v___x_1549_);
return v___x_1551_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__248(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v_z_1554_; lean_object* v___x_1555_; 
v___x_1552_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183);
v___x_1553_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__79));
v_z_1554_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1555_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1554_, v___x_1553_, v___x_1552_);
return v___x_1555_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__249(void){
_start:
{
lean_object* v_ringI_1556_; lean_object* v___x_1557_; 
v_ringI_1556_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__11, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__11_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__11);
v___x_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1557_, 0, v_ringI_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__250(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__249, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__249_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__249);
v___x_1559_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__248, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__248_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__248);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v___x_1558_);
return v___x_1560_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__251(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v_z_1563_; lean_object* v___x_1564_; 
v___x_1561_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183);
v___x_1562_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__82));
v_z_1563_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1564_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1563_, v___x_1562_, v___x_1561_);
return v___x_1564_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__252(void){
_start:
{
lean_object* v_csI_1565_; lean_object* v___x_1566_; 
v_csI_1565_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__19, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__19_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__19);
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_csI_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__253(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__252, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__252_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__252);
v___x_1568_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__251, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__251_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__251);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set(v___x_1569_, 1, v___x_1567_);
return v___x_1569_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__254(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v_z_1572_; lean_object* v___x_1573_; 
v___x_1570_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__183);
v___x_1571_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__85));
v_z_1572_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__0));
v___x_1573_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__1(v_z_1572_, v___x_1571_, v___x_1570_);
return v___x_1573_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__255(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__26, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__26_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__26);
v___x_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__256(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__255, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__255_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__255);
v___x_1577_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__254, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__254_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__254);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v___x_1576_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts(lean_object* v_leLvl_1579_){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v_x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v_x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v_x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v_x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v_x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v_x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1580_ = lean_box(0);
v___x_1581_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__94));
v___x_1582_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__95, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__95_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__95);
lean_inc_n(v_leLvl_1579_, 11);
v___x_1583_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(v_leLvl_1579_, v___x_1580_, v___x_1581_, v___x_1582_);
v___x_1584_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__96, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__96_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__96);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__98));
v___x_1587_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__101, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__101_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__101);
v___x_1588_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(v_leLvl_1579_, v___x_1580_, v___x_1586_, v___x_1587_);
v___x_1589_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__105, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__105_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__105);
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__133, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__133_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__133);
v___x_1592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v_x_1593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1593_, 0, v___x_1585_);
lean_ctor_set(v_x_1593_, 1, v___x_1592_);
v___x_1594_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__138, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__138_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__138);
v___x_1595_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__147, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__147_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__147);
v___x_1596_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__149));
v___x_1597_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(v_leLvl_1579_, v___x_1580_, v___x_1596_, v___x_1582_);
v___x_1598_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__150, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__150_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__150);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__152));
v___x_1601_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(v_leLvl_1579_, v___x_1580_, v___x_1600_, v___x_1582_);
v___x_1602_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__154));
v___x_1603_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__156, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__156_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__156);
v___x_1604_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(v_leLvl_1579_, v___x_1580_, v___x_1602_, v___x_1603_);
v___x_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1601_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__158));
v___x_1608_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(v_leLvl_1579_, v___x_1580_, v___x_1607_, v___x_1582_);
v___x_1609_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__160));
v___x_1610_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(v_leLvl_1579_, v___x_1580_, v___x_1609_, v___x_1603_);
v___x_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
v___x_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1608_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v_x_1593_);
v___x_1614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1606_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1599_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1595_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v_x_1617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1617_, 0, v___x_1594_);
lean_ctor_set(v_x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__164, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__164_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__164);
v___x_1619_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__167, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__167_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__167);
v___x_1620_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__170, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__170_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__170);
v___x_1621_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__182, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__182_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__182);
v___x_1622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
lean_ctor_set(v___x_1622_, 1, v_x_1617_);
v___x_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1620_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1619_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v_x_1625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1625_, 0, v___x_1618_);
lean_ctor_set(v_x_1625_, 1, v___x_1624_);
v___x_1626_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__189, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__189_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__189);
v___x_1627_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__194, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__194_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__194);
v___x_1628_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__199, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__199_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__199);
v___x_1629_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__201, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__201_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__201);
v___x_1630_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__203, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__203_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__203);
v___x_1631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v_x_1625_);
v___x_1632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1629_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1628_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1627_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v_x_1635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1635_, 0, v___x_1626_);
lean_ctor_set(v_x_1635_, 1, v___x_1634_);
v___x_1636_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__204, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__204_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__204);
v___x_1637_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(v_leLvl_1579_, v___x_1580_, v___x_1607_, v___x_1636_);
v___x_1638_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__207, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__207_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__207);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(v_leLvl_1579_, v___x_1580_, v___x_1581_, v___x_1636_);
v___x_1641_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__211, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__211_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__211);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__212, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__212_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__212);
v___x_1644_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(v_leLvl_1579_, v___x_1580_, v___x_1586_, v___x_1643_);
v___x_1645_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__216, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__216_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__216);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__223, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__223_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__223);
v___x_1648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v_x_1635_);
v___x_1649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1646_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1642_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v_x_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1651_, 0, v___x_1639_);
lean_ctor_set(v_x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__225, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__225_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__225);
v___x_1653_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__228, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__228_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__228);
v___x_1654_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__235, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__235_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__235);
v___x_1655_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(v_leLvl_1579_, v___x_1580_, v___x_1596_, v___x_1636_);
v___x_1656_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__236, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__236_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__236);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___lam__0(v_leLvl_1579_, v___x_1580_, v___x_1600_, v___x_1636_);
v___x_1659_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__244, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__244_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__244);
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v_x_1651_);
v___x_1662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1657_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1654_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1653_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v_x_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_x_1665_, 0, v___x_1652_);
lean_ctor_set(v_x_1665_, 1, v___x_1664_);
v___x_1666_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__247, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__247_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__247);
v___x_1667_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__250, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__250_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__250);
v___x_1668_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__253, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__253_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__253);
v___x_1669_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__256, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__256_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__256);
v___x_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v_x_1665_);
v___x_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1668_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1667_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1666_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__107, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__107_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__107);
v___x_1675_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0_spec__0___redArg(v___x_1673_, v___x_1674_);
lean_dec_ref_known(v___x_1673_, 2);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0_spec__0(lean_object* v_as_1676_, lean_object* v_as_x27_1677_, lean_object* v_b_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0_spec__0___redArg(v_as_x27_1677_, v_b_1678_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0_spec__0___boxed(lean_object* v_as_1681_, lean_object* v_as_x27_1682_, lean_object* v_b_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts_spec__0_spec__0(v_as_1681_, v_as_x27_1682_, v_b_1683_, v_a_1684_);
lean_dec(v_as_x27_1682_);
lean_dec(v_as_1681_);
return v_res_1685_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsTypeCarrier___closed__0(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = lean_box(0);
v___x_1687_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts(v___x_1686_);
return v___x_1687_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsTypeCarrier(void){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsTypeCarrier___closed__0, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsTypeCarrier___closed__0_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsTypeCarrier___closed__0);
return v___x_1688_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsSortCarrier___closed__0(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__0, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__0_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier___closed__0);
v___x_1690_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts(v___x_1689_);
return v___x_1690_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsSortCarrier(void){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsSortCarrier___closed__0, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsSortCarrier___closed__0_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsSortCarrier___closed__0);
return v___x_1691_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__0(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36);
v___x_1693_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__14));
v___x_1694_ = l_Lean_mkConst(v___x_1693_, v___x_1692_);
return v___x_1694_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__1(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36);
v___x_1696_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__8));
v___x_1697_ = l_Lean_mkConst(v___x_1696_, v___x_1695_);
return v___x_1697_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__2(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1698_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__5, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__5_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__5);
v___x_1699_ = l_Lean_Int_mkType;
v___x_1700_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__1, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__1_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__1);
v___x_1701_ = l_Lean_mkAppB(v___x_1700_, v___x_1699_, v___x_1698_);
return v___x_1701_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__3(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1702_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__2, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__2_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__2);
v___x_1703_ = l_Lean_Int_mkType;
v___x_1704_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__0, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__0_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__0);
v___x_1705_ = l_Lean_mkAppB(v___x_1704_, v___x_1703_, v___x_1702_);
return v___x_1705_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring(void){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__3, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__3_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring___closed__3);
return v___x_1706_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__0(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinInsts___closed__36);
v___x_1708_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__24));
v___x_1709_ = l_Lean_mkConst(v___x_1708_, v___x_1707_);
return v___x_1709_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__1(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1710_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__52, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__52_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_mkBuiltinAlgebraicInsts___closed__52);
v___x_1711_ = l_Lean_Nat_mkType;
v___x_1712_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__0, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__0_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__0);
v___x_1713_ = l_Lean_mkAppB(v___x_1712_, v___x_1711_, v___x_1710_);
return v___x_1713_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring(void){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__1, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__1_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring___closed__1);
return v___x_1714_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared(lean_object* v_env_1715_, lean_object* v_x_1716_){
_start:
{
switch(lean_obj_tag(v_x_1716_))
{
case 4:
{
lean_object* v_declName_1717_; uint8_t v___x_1718_; uint8_t v___x_1719_; 
v_declName_1717_ = lean_ctor_get(v_x_1716_, 0);
lean_inc(v_declName_1717_);
lean_dec_ref_known(v_x_1716_, 2);
v___x_1718_ = 1;
v___x_1719_ = l_Lean_Environment_contains(v_env_1715_, v_declName_1717_, v___x_1718_);
return v___x_1719_;
}
case 5:
{
lean_object* v_fn_1720_; lean_object* v_arg_1721_; uint8_t v___x_1722_; 
v_fn_1720_ = lean_ctor_get(v_x_1716_, 0);
lean_inc_ref(v_fn_1720_);
v_arg_1721_ = lean_ctor_get(v_x_1716_, 1);
lean_inc_ref(v_arg_1721_);
lean_dec_ref_known(v_x_1716_, 2);
lean_inc_ref(v_env_1715_);
v___x_1722_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared(v_env_1715_, v_fn_1720_);
if (v___x_1722_ == 0)
{
lean_dec_ref(v_arg_1721_);
lean_dec_ref(v_env_1715_);
return v___x_1722_;
}
else
{
v_x_1716_ = v_arg_1721_;
goto _start;
}
}
default: 
{
uint8_t v___x_1724_; 
lean_dec_ref(v_x_1716_);
lean_dec_ref(v_env_1715_);
v___x_1724_ = 1;
return v___x_1724_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared___boxed(lean_object* v_env_1725_, lean_object* v_x_1726_){
_start:
{
uint8_t v_res_1727_; lean_object* v_r_1728_; 
v_res_1727_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared(v_env_1725_, v_x_1726_);
v_r_1728_ = lean_box(v_res_1727_);
return v_r_1728_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__7(void){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = lean_box(0);
v___x_1747_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__6));
v___x_1748_ = l_Lean_mkConst(v___x_1747_, v___x_1746_);
return v___x_1748_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__10(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = lean_box(0);
v___x_1755_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__9));
v___x_1756_ = l_Lean_mkConst(v___x_1755_, v___x_1754_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f(lean_object* v_type_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_type_1757_, v_a_1759_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1856_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1856_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1856_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = l_Lean_Expr_cleanupAnnotations(v_a_1767_);
lean_dec(v_a_1767_);
v___x_1780_ = l_Lean_Expr_isApp(v___x_1779_);
if (v___x_1780_ == 0)
{
lean_dec_ref(v___x_1779_);
lean_del_object(v___x_1769_);
goto v___jp_1763_;
}
else
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1779_);
v___x_1782_ = l_Lean_Expr_isApp(v___x_1781_);
if (v___x_1782_ == 0)
{
lean_dec_ref(v___x_1781_);
lean_dec_ref(v___x_1779_);
lean_del_object(v___x_1769_);
goto v___jp_1763_;
}
else
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1781_);
v___x_1784_ = l_Lean_Expr_isApp(v___x_1783_);
if (v___x_1784_ == 0)
{
lean_dec_ref(v___x_1783_);
lean_dec_ref(v___x_1781_);
lean_dec_ref(v___x_1779_);
lean_del_object(v___x_1769_);
goto v___jp_1763_;
}
else
{
lean_object* v_arg_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v_arg_1785_ = lean_ctor_get(v___x_1783_, 1);
lean_inc_ref(v_arg_1785_);
v___x_1786_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1783_);
lean_dec_ref(v___x_1783_);
v___x_1787_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__2));
v___x_1788_ = l_Lean_Expr_isConstOf(v___x_1786_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
lean_del_object(v___x_1769_);
v___x_1789_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__4));
v___x_1790_ = l_Lean_Expr_isConstOf(v___x_1786_, v___x_1789_);
lean_dec_ref(v___x_1786_);
if (v___x_1790_ == 0)
{
lean_dec_ref(v_arg_1785_);
lean_dec_ref(v___x_1781_);
lean_dec_ref(v___x_1779_);
goto v___jp_1763_;
}
else
{
lean_object* v_arg_1791_; lean_object* v_inst_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v_arg_1838_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v_arg_1791_ = lean_ctor_get(v___x_1779_, 1);
lean_inc_ref(v_arg_1791_);
lean_dec_ref(v___x_1779_);
v_arg_1838_ = lean_ctor_get(v___x_1781_, 1);
lean_inc_ref(v_arg_1838_);
lean_dec_ref(v___x_1781_);
v___x_1845_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17));
v___x_1846_ = l_Lean_Expr_isConstOf(v_arg_1785_, v___x_1845_);
if (v___x_1846_ == 0)
{
goto v___jp_1839_;
}
else
{
lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_intSemiring;
v___x_1848_ = lean_expr_eqv(v_arg_1838_, v___x_1847_);
if (v___x_1848_ == 0)
{
goto v___jp_1839_;
}
else
{
lean_object* v___x_1849_; 
lean_dec_ref(v_arg_1838_);
lean_dec_ref(v_arg_1785_);
v___x_1849_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__10, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__10_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__10);
v_inst_1793_ = v___x_1849_;
v___y_1794_ = v_a_1758_;
v___y_1795_ = v_a_1759_;
v___y_1796_ = v_a_1760_;
v___y_1797_ = v_a_1761_;
goto v___jp_1792_;
}
}
v___jp_1792_:
{
lean_object* v___x_1798_; lean_object* v_env_1799_; uint8_t v___x_1800_; 
v___x_1798_ = lean_st_ref_get(v___y_1797_);
v_env_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc_ref(v_env_1799_);
lean_dec(v___x_1798_);
lean_inc_ref(v_inst_1793_);
v___x_1800_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared(v_env_1799_, v_inst_1793_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec_ref(v_arg_1791_);
v___x_1801_ = lean_box(0);
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; 
lean_inc(v___y_1797_);
lean_inc_ref(v___y_1796_);
lean_inc(v___y_1795_);
lean_inc_ref(v___y_1794_);
lean_inc_ref(v_inst_1793_);
v___x_1803_ = lean_infer_type(v_inst_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v___x_1805_ = l_Lean_Expr_appArg_x21(v_a_1804_);
lean_dec(v_a_1804_);
v___x_1806_ = l_Lean_Meta_isExprDefEq(v_arg_1791_, v___x_1805_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1821_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1821_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1821_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_unbox(v_a_1807_);
lean_dec(v_a_1807_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = lean_box(0);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1812_);
v___x_1814_ = v___x_1809_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
lean_inc_ref(v_inst_1793_);
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v_inst_1793_);
v___x_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1817_);
v___x_1819_ = v___x_1809_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1806_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1806_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec_ref(v_arg_1791_);
v_a_1830_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1803_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1803_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
}
v___jp_1839_:
{
lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1840_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__1));
v___x_1841_ = l_Lean_Expr_isConstOf(v_arg_1785_, v___x_1840_);
lean_dec_ref(v_arg_1785_);
if (v___x_1841_ == 0)
{
lean_dec_ref(v_arg_1838_);
lean_dec_ref(v_arg_1791_);
goto v___jp_1776_;
}
else
{
lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_natSemiring;
v___x_1843_ = lean_expr_eqv(v_arg_1838_, v___x_1842_);
lean_dec_ref(v_arg_1838_);
if (v___x_1843_ == 0)
{
lean_dec_ref(v_arg_1791_);
goto v___jp_1776_;
}
else
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_obj_once(&l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__7, &l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__7_once, _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__7);
v_inst_1793_ = v___x_1844_;
v___y_1794_ = v_a_1758_;
v___y_1795_ = v_a_1759_;
v___y_1796_ = v_a_1760_;
v___y_1797_ = v_a_1761_;
goto v___jp_1792_;
}
}
}
}
}
else
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
lean_dec_ref(v___x_1786_);
lean_dec_ref(v___x_1781_);
lean_dec_ref(v___x_1779_);
v___x_1850_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__17));
v___x_1851_ = l_Lean_Expr_isConstOf(v_arg_1785_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_Lean_Meta_Sym_getBuiltinInstance_x3f___closed__1));
v___x_1853_ = l_Lean_Expr_isConstOf(v_arg_1785_, v___x_1852_);
lean_dec_ref(v_arg_1785_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
lean_del_object(v___x_1769_);
v___x_1854_ = lean_box(0);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
else
{
goto v___jp_1771_;
}
}
else
{
lean_dec_ref(v_arg_1785_);
goto v___jp_1771_;
}
}
}
}
}
v___jp_1771_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = ((lean_object*)(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___closed__0));
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1772_);
v___x_1774_ = v___x_1769_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
v___jp_1776_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_box(0);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
return v___x_1778_;
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
v_a_1857_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1766_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1766_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
v___jp_1763_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f___boxed(lean_object* v_type_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f(v_type_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(lean_object* v_category_1872_, lean_object* v_opts_1873_, lean_object* v_act_1874_, lean_object* v_decl_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_inc(v___y_1879_);
lean_inc_ref(v___y_1878_);
lean_inc(v___y_1877_);
lean_inc_ref(v___y_1876_);
v___x_1881_ = lean_apply_4(v_act_1874_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
v___x_1882_ = l_Lean_profileitIOUnsafe___redArg(v_category_1872_, v_opts_1873_, v___x_1881_, v_decl_1875_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg___boxed(lean_object* v_category_1883_, lean_object* v_opts_1884_, lean_object* v_act_1885_, lean_object* v_decl_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v_category_1883_, v_opts_1884_, v_act_1885_, v_decl_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v_opts_1884_);
lean_dec_ref(v_category_1883_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(lean_object* v_00_u03b1_1893_, lean_object* v_category_1894_, lean_object* v_opts_1895_, lean_object* v_act_1896_, lean_object* v_decl_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v_category_1894_, v_opts_1895_, v_act_1896_, v_decl_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___boxed(lean_object* v_00_u03b1_1904_, lean_object* v_category_1905_, lean_object* v_opts_1906_, lean_object* v_act_1907_, lean_object* v_decl_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(v_00_u03b1_1904_, v_category_1905_, v_opts_1906_, v_act_1907_, v_decl_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec_ref(v_opts_1906_);
lean_dec_ref(v_category_1905_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(lean_object* v_type_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_Lean_leCarrierIsSort(v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1981_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1981_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1981_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___y_1962_; uint8_t v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_unbox(v_a_1957_);
v___x_1976_ = l_Lean_Meta_Sym_getBuiltinInstance_x3f(v___x_1975_, v_type_1915_);
if (lean_obj_tag(v___x_1976_) == 1)
{
lean_object* v___x_1977_; 
lean_del_object(v___x_1959_);
lean_dec(v_a_1957_);
lean_dec_ref(v_type_1915_);
v___x_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
return v___x_1977_;
}
else
{
uint8_t v___x_1978_; 
lean_dec(v___x_1976_);
v___x_1978_ = lean_unbox(v_a_1957_);
lean_dec(v_a_1957_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
v___x_1979_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsTypeCarrier;
v___y_1962_ = v___x_1979_;
goto v___jp_1961_;
}
else
{
lean_object* v___x_1980_; 
v___x_1980_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsSortCarrier;
v___y_1962_ = v___x_1980_;
goto v___jp_1961_;
}
}
v___jp_1961_:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v___y_1962_, v_type_1915_);
if (lean_obj_tag(v___x_1963_) == 1)
{
lean_object* v_val_1964_; lean_object* v___x_1965_; 
v_val_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_val_1964_);
lean_dec_ref_known(v___x_1963_, 1);
v___x_1965_ = lean_st_ref_get(v___y_1919_);
if (lean_obj_tag(v_val_1964_) == 0)
{
lean_object* v___x_1967_; 
lean_dec(v___x_1965_);
lean_dec_ref(v_type_1915_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v_val_1964_);
v___x_1967_ = v___x_1959_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_val_1964_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
else
{
lean_object* v_val_1969_; lean_object* v_env_1970_; uint8_t v___x_1971_; 
v_val_1969_ = lean_ctor_get(v_val_1964_, 0);
v_env_1970_ = lean_ctor_get(v___x_1965_, 0);
lean_inc_ref(v_env_1970_);
lean_dec(v___x_1965_);
lean_inc(v_val_1969_);
v___x_1971_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_isDeclared(v_env_1970_, v_val_1969_);
if (v___x_1971_ == 0)
{
lean_dec_ref_known(v_val_1964_, 1);
lean_del_object(v___x_1959_);
goto v___jp_1921_;
}
else
{
lean_object* v___x_1973_; 
lean_dec_ref(v_type_1915_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v_val_1964_);
v___x_1973_ = v___x_1959_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_val_1964_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
else
{
lean_dec(v___x_1963_);
lean_del_object(v___x_1959_);
goto v___jp_1921_;
}
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec_ref(v_type_1915_);
v_a_1982_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1956_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1956_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
v___jp_1921_:
{
lean_object* v___x_1922_; 
lean_inc_ref(v_type_1915_);
v___x_1922_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinOutParamInst_x3f(v_type_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1947_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1947_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1947_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
if (lean_obj_tag(v_a_1923_) == 1)
{
lean_object* v_val_1927_; lean_object* v___x_1929_; 
lean_dec_ref(v_type_1915_);
v_val_1927_ = lean_ctor_get(v_a_1923_, 0);
lean_inc(v_val_1927_);
lean_dec_ref_known(v_a_1923_, 1);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v_val_1927_);
v___x_1929_ = v___x_1925_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_val_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
else
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
lean_del_object(v___x_1925_);
lean_dec(v_a_1923_);
v___x_1931_ = l_Lean_Meta_isDefEqStuckExceptionId;
v___x_1932_ = lean_box(0);
v___x_1933_ = l_Lean_Meta_synthInstanceCore_x3f(v_type_1915_, v___x_1932_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_1933_) == 0)
{
return v___x_1933_;
}
else
{
lean_object* v_a_1934_; uint8_t v___x_1935_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v___x_1935_ = l_Lean_Exception_isInterrupt(v_a_1934_);
if (v___x_1935_ == 0)
{
uint8_t v___x_1936_; 
lean_inc(v_a_1934_);
v___x_1936_ = l_Lean_Exception_isRuntime(v_a_1934_);
if (v___x_1936_ == 0)
{
if (lean_obj_tag(v_a_1934_) == 0)
{
return v___x_1933_;
}
else
{
lean_object* v_id_1937_; uint8_t v___x_1938_; 
v_id_1937_ = lean_ctor_get(v_a_1934_, 0);
v___x_1938_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1931_, v_id_1937_);
if (v___x_1938_ == 0)
{
return v___x_1933_;
}
else
{
lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v___x_1933_, 0);
lean_dec(v_unused_1946_);
v___x_1940_ = v___x_1933_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_dec(v___x_1933_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1932_);
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1932_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
else
{
return v___x_1933_;
}
}
else
{
return v___x_1933_;
}
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v_type_1915_);
v_a_1948_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1922_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1922_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed(lean_object* v_type_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(v_type_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object* v_type_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___f_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_inc_ref(v_type_1998_);
v___f_2004_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2004_, 0, v_type_1998_);
v___x_2005_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2001_);
v___x_2006_ = ((lean_object*)(l_Lean_Meta_Sym_synthInstanceMeta_x3f___closed__0));
v___x_2007_ = l_Lean_Expr_getAppFn(v_type_1998_);
lean_dec_ref(v_type_1998_);
v___x_2008_ = l_Lean_Expr_constName_x3f(v___x_2007_);
lean_dec_ref(v___x_2007_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v___x_2006_, v___x_2005_, v___f_2004_, v___x_2009_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
lean_dec_ref(v___x_2005_);
return v___x_2010_;
}
else
{
lean_object* v_val_2011_; lean_object* v___x_2012_; 
v_val_2011_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_val_2011_);
lean_dec_ref_known(v___x_2008_, 1);
v___x_2012_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(v___x_2006_, v___x_2005_, v___f_2004_, v_val_2011_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
lean_dec_ref(v___x_2005_);
return v___x_2012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f___boxed(lean_object* v_type_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_){
_start:
{
lean_object* v_ks_2024_; lean_object* v_vs_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2049_; 
v_ks_2024_ = lean_ctor_get(v_x_2020_, 0);
v_vs_2025_ = lean_ctor_get(v_x_2020_, 1);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_x_2020_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2027_ = v_x_2020_;
v_isShared_2028_ = v_isSharedCheck_2049_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_vs_2025_);
lean_inc(v_ks_2024_);
lean_dec(v_x_2020_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2049_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = lean_array_get_size(v_ks_2024_);
v___x_2030_ = lean_nat_dec_lt(v_x_2021_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
lean_dec(v_x_2021_);
v___x_2031_ = lean_array_push(v_ks_2024_, v_x_2022_);
v___x_2032_ = lean_array_push(v_vs_2025_, v_x_2023_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 1, v___x_2032_);
lean_ctor_set(v___x_2027_, 0, v___x_2031_);
v___x_2034_ = v___x_2027_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
else
{
lean_object* v_k_x27_2036_; uint8_t v___x_2037_; 
v_k_x27_2036_ = lean_array_fget_borrowed(v_ks_2024_, v_x_2021_);
v___x_2037_ = lean_expr_eqv(v_x_2022_, v_k_x27_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2039_; 
if (v_isShared_2028_ == 0)
{
v___x_2039_ = v___x_2027_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_ks_2024_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_vs_2025_);
v___x_2039_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_nat_add(v_x_2021_, v___x_2040_);
lean_dec(v_x_2021_);
v_x_2020_ = v___x_2039_;
v_x_2021_ = v___x_2041_;
goto _start;
}
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2044_ = lean_array_fset(v_ks_2024_, v_x_2021_, v_x_2022_);
v___x_2045_ = lean_array_fset(v_vs_2025_, v_x_2021_, v_x_2023_);
lean_dec(v_x_2021_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 1, v___x_2045_);
lean_ctor_set(v___x_2027_, 0, v___x_2044_);
v___x_2047_ = v___x_2027_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2050_, lean_object* v_k_2051_, lean_object* v_v_2052_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_unsigned_to_nat(0u);
v___x_2054_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2050_, v___x_2053_, v_k_2051_, v_v_2052_);
return v___x_2054_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(lean_object* v_x_2056_, size_t v_x_2057_, size_t v_x_2058_, lean_object* v_x_2059_, lean_object* v_x_2060_){
_start:
{
if (lean_obj_tag(v_x_2056_) == 0)
{
lean_object* v_es_2061_; size_t v___x_2062_; size_t v___x_2063_; lean_object* v_j_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v_es_2061_ = lean_ctor_get(v_x_2056_, 0);
v___x_2062_ = ((size_t)31ULL);
v___x_2063_ = lean_usize_land(v_x_2057_, v___x_2062_);
v_j_2064_ = lean_usize_to_nat(v___x_2063_);
v___x_2065_ = lean_array_get_size(v_es_2061_);
v___x_2066_ = lean_nat_dec_lt(v_j_2064_, v___x_2065_);
if (v___x_2066_ == 0)
{
lean_dec(v_j_2064_);
lean_dec(v_x_2060_);
lean_dec_ref(v_x_2059_);
return v_x_2056_;
}
else
{
lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2105_; 
lean_inc_ref(v_es_2061_);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_x_2056_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; 
v_unused_2106_ = lean_ctor_get(v_x_2056_, 0);
lean_dec(v_unused_2106_);
v___x_2068_ = v_x_2056_;
v_isShared_2069_ = v_isSharedCheck_2105_;
goto v_resetjp_2067_;
}
else
{
lean_dec(v_x_2056_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2105_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v_v_2070_; lean_object* v___x_2071_; lean_object* v_xs_x27_2072_; lean_object* v___y_2074_; 
v_v_2070_ = lean_array_fget(v_es_2061_, v_j_2064_);
v___x_2071_ = lean_box(0);
v_xs_x27_2072_ = lean_array_fset(v_es_2061_, v_j_2064_, v___x_2071_);
switch(lean_obj_tag(v_v_2070_))
{
case 0:
{
lean_object* v_key_2079_; lean_object* v_val_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2090_; 
v_key_2079_ = lean_ctor_get(v_v_2070_, 0);
v_val_2080_ = lean_ctor_get(v_v_2070_, 1);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_v_2070_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2082_ = v_v_2070_;
v_isShared_2083_ = v_isSharedCheck_2090_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_val_2080_);
lean_inc(v_key_2079_);
lean_dec(v_v_2070_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2090_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_expr_eqv(v_x_2059_, v_key_2079_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_del_object(v___x_2082_);
v___x_2085_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2079_, v_val_2080_, v_x_2059_, v_x_2060_);
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
v___y_2074_ = v___x_2086_;
goto v___jp_2073_;
}
else
{
lean_object* v___x_2088_; 
lean_dec(v_val_2080_);
lean_dec(v_key_2079_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 1, v_x_2060_);
lean_ctor_set(v___x_2082_, 0, v_x_2059_);
v___x_2088_ = v___x_2082_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_x_2059_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_x_2060_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
v___y_2074_ = v___x_2088_;
goto v___jp_2073_;
}
}
}
}
case 1:
{
lean_object* v_node_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2103_; 
v_node_2091_ = lean_ctor_get(v_v_2070_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_v_2070_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2093_ = v_v_2070_;
v_isShared_2094_ = v_isSharedCheck_2103_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_node_2091_);
lean_dec(v_v_2070_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2103_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
size_t v___x_2095_; size_t v___x_2096_; size_t v___x_2097_; size_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2095_ = ((size_t)5ULL);
v___x_2096_ = lean_usize_shift_right(v_x_2057_, v___x_2095_);
v___x_2097_ = ((size_t)1ULL);
v___x_2098_ = lean_usize_add(v_x_2058_, v___x_2097_);
v___x_2099_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_node_2091_, v___x_2096_, v___x_2098_, v_x_2059_, v_x_2060_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2099_);
v___x_2101_ = v___x_2093_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
v___y_2074_ = v___x_2101_;
goto v___jp_2073_;
}
}
}
default: 
{
lean_object* v___x_2104_; 
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v_x_2059_);
lean_ctor_set(v___x_2104_, 1, v_x_2060_);
v___y_2074_ = v___x_2104_;
goto v___jp_2073_;
}
}
v___jp_2073_:
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2075_ = lean_array_fset(v_xs_x27_2072_, v_j_2064_, v___y_2074_);
lean_dec(v_j_2064_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v___x_2075_);
v___x_2077_ = v___x_2068_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
else
{
lean_object* v_ks_2107_; lean_object* v_vs_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2126_; 
v_ks_2107_ = lean_ctor_get(v_x_2056_, 0);
v_vs_2108_ = lean_ctor_get(v_x_2056_, 1);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_x_2056_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2110_ = v_x_2056_;
v_isShared_2111_ = v_isSharedCheck_2126_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_vs_2108_);
lean_inc(v_ks_2107_);
lean_dec(v_x_2056_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2126_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_ks_2107_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_vs_2108_);
v___x_2113_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v_newNode_2114_; size_t v___x_2115_; uint8_t v___x_2116_; 
v_newNode_2114_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(v___x_2113_, v_x_2059_, v_x_2060_);
v___x_2115_ = ((size_t)7ULL);
v___x_2116_ = lean_usize_dec_le(v___x_2115_, v_x_2058_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2117_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2114_);
v___x_2118_ = lean_unsigned_to_nat(4u);
v___x_2119_ = lean_nat_dec_lt(v___x_2117_, v___x_2118_);
lean_dec(v___x_2117_);
if (v___x_2119_ == 0)
{
lean_object* v_ks_2120_; lean_object* v_vs_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_ks_2120_ = lean_ctor_get(v_newNode_2114_, 0);
lean_inc_ref(v_ks_2120_);
v_vs_2121_ = lean_ctor_get(v_newNode_2114_, 1);
lean_inc_ref(v_vs_2121_);
lean_dec_ref(v_newNode_2114_);
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___closed__0);
v___x_2124_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_x_2058_, v_ks_2120_, v_vs_2121_, v___x_2122_, v___x_2123_);
lean_dec_ref(v_vs_2121_);
lean_dec_ref(v_ks_2120_);
return v___x_2124_;
}
else
{
return v_newNode_2114_;
}
}
else
{
return v_newNode_2114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(size_t v_depth_2127_, lean_object* v_keys_2128_, lean_object* v_vals_2129_, lean_object* v_i_2130_, lean_object* v_entries_2131_){
_start:
{
lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = lean_array_get_size(v_keys_2128_);
v___x_2133_ = lean_nat_dec_lt(v_i_2130_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_dec(v_i_2130_);
return v_entries_2131_;
}
else
{
lean_object* v_k_2134_; lean_object* v_v_2135_; uint64_t v___x_2136_; size_t v_h_2137_; size_t v___x_2138_; lean_object* v___x_2139_; size_t v___x_2140_; size_t v___x_2141_; size_t v___x_2142_; size_t v_h_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_k_2134_ = lean_array_fget_borrowed(v_keys_2128_, v_i_2130_);
v_v_2135_ = lean_array_fget_borrowed(v_vals_2129_, v_i_2130_);
v___x_2136_ = l_Lean_Expr_hash(v_k_2134_);
v_h_2137_ = lean_uint64_to_usize(v___x_2136_);
v___x_2138_ = ((size_t)5ULL);
v___x_2139_ = lean_unsigned_to_nat(1u);
v___x_2140_ = ((size_t)1ULL);
v___x_2141_ = lean_usize_sub(v_depth_2127_, v___x_2140_);
v___x_2142_ = lean_usize_mul(v___x_2138_, v___x_2141_);
v_h_2143_ = lean_usize_shift_right(v_h_2137_, v___x_2142_);
v___x_2144_ = lean_nat_add(v_i_2130_, v___x_2139_);
lean_dec(v_i_2130_);
lean_inc(v_v_2135_);
lean_inc(v_k_2134_);
v___x_2145_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_entries_2131_, v_h_2143_, v_depth_2127_, v_k_2134_, v_v_2135_);
v_i_2130_ = v___x_2144_;
v_entries_2131_ = v___x_2145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2147_, lean_object* v_keys_2148_, lean_object* v_vals_2149_, lean_object* v_i_2150_, lean_object* v_entries_2151_){
_start:
{
size_t v_depth_boxed_2152_; lean_object* v_res_2153_; 
v_depth_boxed_2152_ = lean_unbox_usize(v_depth_2147_);
lean_dec(v_depth_2147_);
v_res_2153_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2152_, v_keys_2148_, v_vals_2149_, v_i_2150_, v_entries_2151_);
lean_dec_ref(v_vals_2149_);
lean_dec_ref(v_keys_2148_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg___boxed(lean_object* v_x_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_){
_start:
{
size_t v_x_740__boxed_2159_; size_t v_x_741__boxed_2160_; lean_object* v_res_2161_; 
v_x_740__boxed_2159_ = lean_unbox_usize(v_x_2155_);
lean_dec(v_x_2155_);
v_x_741__boxed_2160_ = lean_unbox_usize(v_x_2156_);
lean_dec(v_x_2156_);
v_res_2161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_2154_, v_x_740__boxed_2159_, v_x_741__boxed_2160_, v_x_2157_, v_x_2158_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_){
_start:
{
uint64_t v___x_2165_; size_t v___x_2166_; size_t v___x_2167_; lean_object* v___x_2168_; 
v___x_2165_ = l_Lean_Expr_hash(v_x_2163_);
v___x_2166_ = lean_uint64_to_usize(v___x_2165_);
v___x_2167_ = ((size_t)1ULL);
v___x_2168_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_2162_, v___x_2166_, v___x_2167_, v_x_2163_, v_x_2164_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object* v_type_2169_, lean_object* v_inst_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___x_2173_; lean_object* v_share_2174_; lean_object* v_maxFVar_2175_; lean_object* v_proofInstInfo_2176_; lean_object* v_proofInstInfoFVar_2177_; lean_object* v_letValue_2178_; lean_object* v_inferType_2179_; lean_object* v_getLevel_2180_; lean_object* v_congrInfo_2181_; lean_object* v_defEqI_2182_; lean_object* v_extensions_2183_; lean_object* v_issues_2184_; lean_object* v_canon_2185_; lean_object* v_instanceOverrides_2186_; uint8_t v_debug_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2198_; 
v___x_2173_ = lean_st_ref_take(v_a_2171_);
v_share_2174_ = lean_ctor_get(v___x_2173_, 0);
v_maxFVar_2175_ = lean_ctor_get(v___x_2173_, 1);
v_proofInstInfo_2176_ = lean_ctor_get(v___x_2173_, 2);
v_proofInstInfoFVar_2177_ = lean_ctor_get(v___x_2173_, 3);
v_letValue_2178_ = lean_ctor_get(v___x_2173_, 4);
v_inferType_2179_ = lean_ctor_get(v___x_2173_, 5);
v_getLevel_2180_ = lean_ctor_get(v___x_2173_, 6);
v_congrInfo_2181_ = lean_ctor_get(v___x_2173_, 7);
v_defEqI_2182_ = lean_ctor_get(v___x_2173_, 8);
v_extensions_2183_ = lean_ctor_get(v___x_2173_, 9);
v_issues_2184_ = lean_ctor_get(v___x_2173_, 10);
v_canon_2185_ = lean_ctor_get(v___x_2173_, 11);
v_instanceOverrides_2186_ = lean_ctor_get(v___x_2173_, 12);
v_debug_2187_ = lean_ctor_get_uint8(v___x_2173_, sizeof(void*)*13);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2189_ = v___x_2173_;
v_isShared_2190_ = v_isSharedCheck_2198_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_instanceOverrides_2186_);
lean_inc(v_canon_2185_);
lean_inc(v_issues_2184_);
lean_inc(v_extensions_2183_);
lean_inc(v_defEqI_2182_);
lean_inc(v_congrInfo_2181_);
lean_inc(v_getLevel_2180_);
lean_inc(v_inferType_2179_);
lean_inc(v_letValue_2178_);
lean_inc(v_proofInstInfoFVar_2177_);
lean_inc(v_proofInstInfo_2176_);
lean_inc(v_maxFVar_2175_);
lean_inc(v_share_2174_);
lean_dec(v___x_2173_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2198_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2191_ = lean_box(0);
v___x_2192_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(v_instanceOverrides_2186_, v_type_2169_, v_inst_2170_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 12, v___x_2192_);
v___x_2194_ = v___x_2189_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_share_2174_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_maxFVar_2175_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v_proofInstInfo_2176_);
lean_ctor_set(v_reuseFailAlloc_2197_, 3, v_proofInstInfoFVar_2177_);
lean_ctor_set(v_reuseFailAlloc_2197_, 4, v_letValue_2178_);
lean_ctor_set(v_reuseFailAlloc_2197_, 5, v_inferType_2179_);
lean_ctor_set(v_reuseFailAlloc_2197_, 6, v_getLevel_2180_);
lean_ctor_set(v_reuseFailAlloc_2197_, 7, v_congrInfo_2181_);
lean_ctor_set(v_reuseFailAlloc_2197_, 8, v_defEqI_2182_);
lean_ctor_set(v_reuseFailAlloc_2197_, 9, v_extensions_2183_);
lean_ctor_set(v_reuseFailAlloc_2197_, 10, v_issues_2184_);
lean_ctor_set(v_reuseFailAlloc_2197_, 11, v_canon_2185_);
lean_ctor_set(v_reuseFailAlloc_2197_, 12, v___x_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2197_, sizeof(void*)*13, v_debug_2187_);
v___x_2194_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = lean_st_ref_put(v_a_2171_, v___x_2194_);
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2191_);
return v___x_2196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___redArg___boxed(lean_object* v_type_2199_, lean_object* v_inst_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Meta_Sym_registerInstance___redArg(v_type_2199_, v_inst_2200_, v_a_2201_);
lean_dec(v_a_2201_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance(lean_object* v_type_2204_, lean_object* v_inst_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_Meta_Sym_registerInstance___redArg(v_type_2204_, v_inst_2205_, v_a_2207_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerInstance___boxed(lean_object* v_type_2214_, lean_object* v_inst_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_Meta_Sym_registerInstance(v_type_2214_, v_inst_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0(lean_object* v_00_u03b2_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_, lean_object* v_x_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0___redArg(v_x_2225_, v_x_2226_, v_x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0(lean_object* v_00_u03b2_2229_, lean_object* v_x_2230_, size_t v_x_2231_, size_t v_x_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___redArg(v_x_2230_, v_x_2231_, v_x_2232_, v_x_2233_, v_x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_, lean_object* v_x_2239_, lean_object* v_x_2240_, lean_object* v_x_2241_){
_start:
{
size_t v_x_946__boxed_2242_; size_t v_x_947__boxed_2243_; lean_object* v_res_2244_; 
v_x_946__boxed_2242_ = lean_unbox_usize(v_x_2238_);
lean_dec(v_x_2238_);
v_x_947__boxed_2243_ = lean_unbox_usize(v_x_2239_);
lean_dec(v_x_2239_);
v_res_2244_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0(v_00_u03b2_2236_, v_x_2237_, v_x_946__boxed_2242_, v_x_947__boxed_2243_, v_x_2240_, v_x_2241_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2245_, lean_object* v_n_2246_, lean_object* v_k_2247_, lean_object* v_v_2248_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1___redArg(v_n_2246_, v_k_2247_, v_v_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2250_, size_t v_depth_2251_, lean_object* v_keys_2252_, lean_object* v_vals_2253_, lean_object* v_heq_2254_, lean_object* v_i_2255_, lean_object* v_entries_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___redArg(v_depth_2251_, v_keys_2252_, v_vals_2253_, v_i_2255_, v_entries_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2258_, lean_object* v_depth_2259_, lean_object* v_keys_2260_, lean_object* v_vals_2261_, lean_object* v_heq_2262_, lean_object* v_i_2263_, lean_object* v_entries_2264_){
_start:
{
size_t v_depth_boxed_2265_; lean_object* v_res_2266_; 
v_depth_boxed_2265_ = lean_unbox_usize(v_depth_2259_);
lean_dec(v_depth_2259_);
v_res_2266_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__2(v_00_u03b2_2258_, v_depth_boxed_2265_, v_keys_2260_, v_vals_2261_, v_heq_2262_, v_i_2263_, v_entries_2264_);
lean_dec_ref(v_vals_2261_);
lean_dec_ref(v_keys_2260_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2267_, lean_object* v_x_2268_, lean_object* v_x_2269_, lean_object* v_x_2270_, lean_object* v_x_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_registerInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2268_, v_x_2269_, v_x_2270_, v_x_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2273_, lean_object* v_vals_2274_, lean_object* v_i_2275_, lean_object* v_k_2276_){
_start:
{
lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2277_ = lean_array_get_size(v_keys_2273_);
v___x_2278_ = lean_nat_dec_lt(v_i_2275_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; 
lean_dec(v_i_2275_);
v___x_2279_ = lean_box(0);
return v___x_2279_;
}
else
{
lean_object* v_k_x27_2280_; uint8_t v___x_2281_; 
v_k_x27_2280_ = lean_array_fget_borrowed(v_keys_2273_, v_i_2275_);
v___x_2281_ = lean_expr_eqv(v_k_2276_, v_k_x27_2280_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_unsigned_to_nat(1u);
v___x_2283_ = lean_nat_add(v_i_2275_, v___x_2282_);
lean_dec(v_i_2275_);
v_i_2275_ = v___x_2283_;
goto _start;
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_array_fget_borrowed(v_vals_2274_, v_i_2275_);
lean_dec(v_i_2275_);
lean_inc(v___x_2285_);
v___x_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2287_, lean_object* v_vals_2288_, lean_object* v_i_2289_, lean_object* v_k_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2287_, v_vals_2288_, v_i_2289_, v_k_2290_);
lean_dec_ref(v_k_2290_);
lean_dec_ref(v_vals_2288_);
lean_dec_ref(v_keys_2287_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(lean_object* v_x_2292_, size_t v_x_2293_, lean_object* v_x_2294_){
_start:
{
if (lean_obj_tag(v_x_2292_) == 0)
{
lean_object* v_es_2295_; lean_object* v___x_2296_; size_t v___x_2297_; size_t v___x_2298_; lean_object* v_j_2299_; lean_object* v___x_2300_; 
v_es_2295_ = lean_ctor_get(v_x_2292_, 0);
v___x_2296_ = lean_box(2);
v___x_2297_ = ((size_t)31ULL);
v___x_2298_ = lean_usize_land(v_x_2293_, v___x_2297_);
v_j_2299_ = lean_usize_to_nat(v___x_2298_);
v___x_2300_ = lean_array_get_borrowed(v___x_2296_, v_es_2295_, v_j_2299_);
lean_dec(v_j_2299_);
switch(lean_obj_tag(v___x_2300_))
{
case 0:
{
lean_object* v_key_2301_; lean_object* v_val_2302_; uint8_t v___x_2303_; 
v_key_2301_ = lean_ctor_get(v___x_2300_, 0);
v_val_2302_ = lean_ctor_get(v___x_2300_, 1);
v___x_2303_ = lean_expr_eqv(v_x_2294_, v_key_2301_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_box(0);
return v___x_2304_;
}
else
{
lean_object* v___x_2305_; 
lean_inc(v_val_2302_);
v___x_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2305_, 0, v_val_2302_);
return v___x_2305_;
}
}
case 1:
{
lean_object* v_node_2306_; size_t v___x_2307_; size_t v___x_2308_; 
v_node_2306_ = lean_ctor_get(v___x_2300_, 0);
v___x_2307_ = ((size_t)5ULL);
v___x_2308_ = lean_usize_shift_right(v_x_2293_, v___x_2307_);
v_x_2292_ = v_node_2306_;
v_x_2293_ = v___x_2308_;
goto _start;
}
default: 
{
lean_object* v___x_2310_; 
v___x_2310_ = lean_box(0);
return v___x_2310_;
}
}
}
else
{
lean_object* v_ks_2311_; lean_object* v_vs_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_ks_2311_ = lean_ctor_get(v_x_2292_, 0);
v_vs_2312_ = lean_ctor_get(v_x_2292_, 1);
v___x_2313_ = lean_unsigned_to_nat(0u);
v___x_2314_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2311_, v_vs_2312_, v___x_2313_, v_x_2294_);
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2315_, lean_object* v_x_2316_, lean_object* v_x_2317_){
_start:
{
size_t v_x_747__boxed_2318_; lean_object* v_res_2319_; 
v_x_747__boxed_2318_ = lean_unbox_usize(v_x_2316_);
lean_dec(v_x_2316_);
v_res_2319_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_2315_, v_x_747__boxed_2318_, v_x_2317_);
lean_dec_ref(v_x_2317_);
lean_dec_ref(v_x_2315_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(lean_object* v_x_2320_, lean_object* v_x_2321_){
_start:
{
uint64_t v___x_2322_; size_t v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = l_Lean_Expr_hash(v_x_2321_);
v___x_2323_ = lean_uint64_to_usize(v___x_2322_);
v___x_2324_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_2320_, v___x_2323_, v_x_2321_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg___boxed(lean_object* v_x_2325_, lean_object* v_x_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_x_2325_, v_x_2326_);
lean_dec_ref(v_x_2326_);
lean_dec_ref(v_x_2325_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object* v_type_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v___x_2335_; lean_object* v_instanceOverrides_2336_; lean_object* v___x_2337_; 
v___x_2335_ = lean_st_ref_get(v_a_2329_);
v_instanceOverrides_2336_ = lean_ctor_get(v___x_2335_, 12);
lean_inc_ref(v_instanceOverrides_2336_);
lean_dec(v___x_2335_);
v___x_2337_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_instanceOverrides_2336_, v_type_2328_);
lean_dec_ref(v_instanceOverrides_2336_);
if (lean_obj_tag(v___x_2337_) == 1)
{
lean_object* v___x_2338_; 
lean_dec_ref(v_type_2328_);
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
return v___x_2338_;
}
else
{
lean_object* v___x_2339_; 
lean_dec(v___x_2337_);
v___x_2339_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_2328_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
return v___x_2339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg___boxed(lean_object* v_type_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec(v_a_2341_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f(lean_object* v_type_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_2348_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance_x3f___boxed(lean_object* v_type_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_Meta_Sym_synthInstance_x3f(v_type_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0(lean_object* v_00_u03b2_2366_, lean_object* v_x_2367_, lean_object* v_x_2368_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___redArg(v_x_2367_, v_x_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0___boxed(lean_object* v_00_u03b2_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0(v_00_u03b2_2370_, v_x_2371_, v_x_2372_);
lean_dec_ref(v_x_2372_);
lean_dec_ref(v_x_2371_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2374_, lean_object* v_x_2375_, size_t v_x_2376_, lean_object* v_x_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___redArg(v_x_2375_, v_x_2376_, v_x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_){
_start:
{
size_t v_x_831__boxed_2383_; lean_object* v_res_2384_; 
v_x_831__boxed_2383_ = lean_unbox_usize(v_x_2381_);
lean_dec(v_x_2381_);
v_res_2384_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0(v_00_u03b2_2379_, v_x_2380_, v_x_831__boxed_2383_, v_x_2382_);
lean_dec_ref(v_x_2382_);
lean_dec_ref(v_x_2380_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2385_, lean_object* v_keys_2386_, lean_object* v_vals_2387_, lean_object* v_heq_2388_, lean_object* v_i_2389_, lean_object* v_k_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2386_, v_vals_2387_, v_i_2389_, v_k_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2392_, lean_object* v_keys_2393_, lean_object* v_vals_2394_, lean_object* v_heq_2395_, lean_object* v_i_2396_, lean_object* v_k_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_synthInstance_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2392_, v_keys_2393_, v_vals_2394_, v_heq_2395_, v_i_2396_, v_k_2397_);
lean_dec_ref(v_k_2397_);
lean_dec_ref(v_vals_2394_);
lean_dec_ref(v_keys_2393_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(lean_object* v_msgData_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; lean_object* v_env_2406_; uint8_t v___x_2407_; lean_object* v_env_2408_; lean_object* v___x_2409_; lean_object* v_toCold_2410_; lean_object* v_mctx_2411_; lean_object* v_lctx_2412_; lean_object* v_options_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2405_ = lean_st_ref_get(v___y_2403_);
v_env_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc_ref(v_env_2406_);
lean_dec(v___x_2405_);
v___x_2407_ = 0;
v_env_2408_ = l_Lean_Environment_setRecordingDeps(v_env_2406_, v___x_2407_);
v___x_2409_ = lean_st_ref_get(v___y_2401_);
v_toCold_2410_ = lean_ctor_get(v___y_2402_, 0);
v_mctx_2411_ = lean_ctor_get(v___x_2409_, 0);
lean_inc_ref(v_mctx_2411_);
lean_dec(v___x_2409_);
v_lctx_2412_ = lean_ctor_get(v___y_2400_, 2);
v_options_2413_ = lean_ctor_get(v_toCold_2410_, 2);
lean_inc_ref(v_options_2413_);
lean_inc_ref(v_lctx_2412_);
v___x_2414_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2414_, 0, v_env_2408_);
lean_ctor_set(v___x_2414_, 1, v_mctx_2411_);
lean_ctor_set(v___x_2414_, 2, v_lctx_2412_);
lean_ctor_set(v___x_2414_, 3, v_options_2413_);
v___x_2415_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v_msgData_2399_);
v___x_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0___boxed(lean_object* v_msgData_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(v_msgData_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(lean_object* v_msg_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_ref_2430_; lean_object* v___x_2431_; lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2440_; 
v_ref_2430_ = lean_ctor_get(v___y_2427_, 2);
v___x_2431_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(v_msg_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
lean_inc(v_ref_2430_);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v_ref_2430_);
lean_ctor_set(v___x_2436_, 1, v_a_2432_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set_tag(v___x_2434_, 1);
lean_ctor_set(v___x_2434_, 0, v___x_2436_);
v___x_2438_ = v___x_2434_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg___boxed(lean_object* v_msg_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v_msg_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
return v_res_2447_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_synthInstance___closed__1(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = ((lean_object*)(l_Lean_Meta_Sym_synthInstance___closed__0));
v___x_2450_ = l_Lean_stringToMessageData(v___x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance(lean_object* v_type_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v___x_2459_; 
lean_inc_ref(v_type_2451_);
v___x_2459_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_2451_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2472_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2472_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2472_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
if (lean_obj_tag(v_a_2460_) == 1)
{
lean_object* v_val_2464_; lean_object* v___x_2466_; 
lean_dec_ref(v_type_2451_);
v_val_2464_ = lean_ctor_get(v_a_2460_, 0);
lean_inc(v_val_2464_);
lean_dec_ref_known(v_a_2460_, 1);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v_val_2464_);
v___x_2466_ = v___x_2462_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_val_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
else
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_del_object(v___x_2462_);
lean_dec(v_a_2460_);
v___x_2468_ = lean_obj_once(&l_Lean_Meta_Sym_synthInstance___closed__1, &l_Lean_Meta_Sym_synthInstance___closed__1_once, _init_l_Lean_Meta_Sym_synthInstance___closed__1);
v___x_2469_ = l_Lean_indentExpr(v_type_2451_);
v___x_2470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2468_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v___x_2470_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
return v___x_2471_;
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref(v_type_2451_);
v_a_2473_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2459_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2459_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstance___boxed(lean_object* v_type_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_Meta_Sym_synthInstance(v_type_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0(lean_object* v_00_u03b1_2490_, lean_object* v_msg_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(v_msg_2491_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___boxed(lean_object* v_00_u03b1_2500_, lean_object* v_msg_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0(v_00_u03b1_2500_, v_msg_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(lean_object* v_x_2510_, lean_object* v_type_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2530_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2530_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2530_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
if (lean_obj_tag(v_a_2519_) == 1)
{
lean_object* v_val_2523_; lean_object* v___x_2524_; 
lean_del_object(v___x_2521_);
v_val_2523_ = lean_ctor_get(v_a_2519_, 0);
lean_inc(v_val_2523_);
lean_dec_ref_known(v_a_2519_, 1);
v___x_2524_ = l_Lean_Meta_isExprDefEq(v_x_2510_, v_val_2523_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
return v___x_2524_;
}
else
{
uint8_t v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
lean_dec(v_a_2519_);
lean_dec_ref(v_x_2510_);
v___x_2525_ = 0;
v___x_2526_ = lean_box(v___x_2525_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2526_);
v___x_2528_ = v___x_2521_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v_x_2510_);
v_a_2531_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2518_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2518_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___redArg___boxed(lean_object* v_x_2539_, lean_object* v_type_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_x_2539_, v_type_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign(lean_object* v_x_2548_, lean_object* v_type_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_x_2548_, v_type_2549_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_synthInstanceAndAssign___boxed(lean_object* v_x_2558_, lean_object* v_type_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_Meta_Sym_synthInstanceAndAssign(v_x_2558_, v_type_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
return v_res_2567_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* runtime_initialize_Init_GrindInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Int(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Package(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
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
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier = _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier();
lean_mark_persistent(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsTypeCarrier);
l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier = _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier();
lean_mark_persistent(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInstsSortCarrier);
l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsTypeCarrier = _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsTypeCarrier();
lean_mark_persistent(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsTypeCarrier);
l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsSortCarrier = _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsSortCarrier();
lean_mark_persistent(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinAlgebraicInstsSortCarrier);
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
lean_object* initialize_Lean_CoreM(uint8_t builtin);
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
res = initialize_Lean_CoreM(builtin);
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
